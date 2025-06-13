#-*- coding:utf-8 -*-
#
#
#   Layout  Module
#
#   unittesting in tests/test_layout_u.py
#
"""
.. currentmodule:: pylayers.gis.layout

.. autosummary::

"""

try:
    from tvtk.api import tvtk
    from mayavi import mlab
except ImportError:
    print('Layout:Mayavi is not installed')

import sys
import os
import copy
import glob
import time
import tqdm
import numpy as np
import numpy.random as rd
import scipy as sp
import scipy.sparse as sparse
import doctest
import triangle
import matplotlib.pyplot as plt
import matplotlib.colors as clr
import networkx as nx
import pandas as pd
from itertools import combinations, product
import ast
from networkx.readwrite import write_graphml, read_graphml
from pylayers.util.basemap_compat import Basemap
import shapely.geometry as sh
import shapefile as shp
from shapely.ops import unary_union
from matplotlib.patches import Polygon as PolygonPatch
from numpy import array
import PIL.Image as Image
import hashlib
import pylayers.gis.kml as gkml
from functools import partial
import pickle
import configparser as ConfigParser
from urllib.request import urlopen


import pylayers.antprop.slab as sb
from pylayers.util import geomutil as geu
from pylayers.util import plotutil as plu
from pylayers.util import pyutil as pyu
from pylayers.util import graphutil as gru
from pylayers.util import cone
import pylayers.gis.furniture as fur
import pylayers.gis.osmparser as osm
from pylayers.gis.selectl import SelectL
import pylayers.util.graphutil as gph
import pylayers.util.project as pro
from pylayers.util.project import logger

def _convert_attributes(graph):
    """Convert string attributes from GraphML back to Python objects."""
    for n, d in graph.nodes(data=True):
        for k, v in d.items():
            if isinstance(v, str):
                try:
                    d[k] = ast.literal_eval(v)
                except (ValueError, SyntaxError):
                    pass  # keep as string if it's not a literal
    for u, v, d in graph.edges(data=True):
        for k, val in d.items():
            if isinstance(val, str):
                try:
                    d[k] = ast.literal_eval(val)
                except (ValueError, SyntaxError):
                    pass  # keep as string if it's not a literal
    return graph


def pbar(verbose,**kwargs):
    if verbose:
        pbar=tqdm.tqdm(**kwargs)
        return pbar


class Layout(pro.PyLayers):
    """ Handling Layout

    Attributes
    ----------

    Gs     : Graph of points and segment (structure)
    Gt     : Graph of convex cycles      (topology)
    Gv     : Graph of visibility         (visibility)
    Gi     : Graph of interactions       (interactions)
    Gr     : Graph of rooms              (rooms)
    Nnode  : Number of nodes of Gs
    Nedge  : Number of edges of Gs
    pt     : points sequence
    tahe   : tail head
    """
    def __init__(self,arg='',**kwargs):
        """ object constructor

        Parameters
        ----------

        arg : string or tuple
            layout file name, address or (lat,lon) or '(lat,lon)'
        mat :
            material dB file name
        slab :
            slab dB file name
        fur :
            furniture file name
        force : boolean
        check : boolean
        build : boolean
        verbose : boolean
        bcartesian : boolean
        xlim : '(xmin,xmax,ymin,ymax) | () default'
        dist_m : int
        typ : string
            'indoor' | 'outdoor'


        """
        self.arg = arg

        self._filematini = kwargs.pop('mat','matDB.ini')
        self._fileslabini = kwargs.pop('slab','slabDB.ini')
        self._filefur = kwargs.pop('fur','')
        self.bcheck = kwargs.pop('bcheck',False)
        self.bbuild = kwargs.pop('bbuild',False)
        self.bgraphs = kwargs.pop('bgraphs',False)
        self.bverbose = kwargs.pop('bverbose',False)
        self.bcartesian = kwargs.pop('bcartesian',True)
        self.xlim = kwargs.pop('xlim',())
        self.dist_m = kwargs.pop('dist_m',400)
        self.typ = kwargs.pop('typ','outdoor')

        self.labels = {}

        self.Np = 0
        self.Ns = 0
        self.Nss = 0
        self.lsss = []

        #
        # Initializing graphs
        # Gs Gr Gt Gm

        self.Gs = nx.Graph(name='Gs')
        self.Gr = nx.Graph(name='Gr')
        self.Gt = nx.Graph(name='Gt')
        self.Gm = nx.Graph(name='Gm')

        self.Gs.pos = {}
        self.tahe = np.zeros(([2, 0]), dtype=int)
        self.lbltg = []

        self.Gt.pos = {}
        self._shseg = {}

        self.hasboundary = False
        self.coordinates = 'cart'
        self.version = '1.3'

        assert(self.typ in ['indoor','outdoor','floorplan'])

        self.isbuilt = False
        self.loadosm = False

        #
        # setting display option

        self.display = {}
        self.display['title'] = ''
        self.display['ticksoff'] = True
        self.display['nodes'] = False
        self.display['ndsize'] = 10
        self.display['ndlabel'] = False
        self.display['ndlblsize'] = 20
        self.display['edlblsize'] = 20
        self.display['fontsize'] = 20
        self.display['edlabel'] = False
        self.display['edges'] = True
        self.display['ednodes'] = False
        self.display['subseg'] = True
        self.display['isonb'] = True
        self.display['transition'] = True
        self.display['visu'] = False
        self.display['thin'] = False
        self.display['scaled'] = True
        self.display['alpha'] = 0.5
        self.display['layer'] = []
        self.display['clear'] = False
        self.display['activelayer'] = 'AIR'
        self.display['layers'] = []
        self.display['overlay'] = False
        self.display['overlay_flip'] = ""
        self.display['overlay_file'] = ""
        self.display['overlay_axis'] = ""

        if self.xlim!=():
            self.display['box']= self.xlim
        else:
            self.display['box'] = (-50, 50, -50, 50)

        self.name = {}
        self.ax = self.display['box']
        self.zmin = 0
        self.maxheight = 3.

        newfile = False
        loadlay = False
        loadosm = False
        loadres = False

        if type(self.arg)==tuple:
            self.arg = str(self.arg)

        self.dfpoi = pd.DataFrame(columns=['name','type','lon','lat','alt','x',',y','z','radius'])
        if type(self.arg) is bytes:
            self.arg = self.arg.decode('utf-8')

        arg, ext = os.path.splitext(self.arg)
        if arg != '':
            if ext == '.ini':
                self._filename = self.arg
                loadlay = True
            if ext == '.lay':
                self._filename = self.arg
                loadlay = True
            elif ext == '.osm':
                self._filename = arg + '.lay'
                loadosm = True
            elif ext == '.res':
                self._filename = arg + '.lay'
                loadres = True
            else:
                self.typ = 'outdoor'
        else:  # No argument
            self._filename = 'newfile.lay'
            newfile = True
            self.sl = sb.SlabDB(fileslab=self._fileslabini, filemat=self._filematini)
            self.zfloor = 0.
            self.zceil = self.maxheight

        if not newfile:
            if loadlay:
                filename = pyu.getlong(self._filename, pro.pstruc['DIRLAY'])
                if os.path.exists(filename):
                    self.load()
                else:
                    newfile = True
                    print("new file - creating a void Layout", self._filename)
            elif loadosm:
                self.importosm(fileosm=self.arg, cart=self.bcartesian, typ=self.typ)
                self.loadosm = True
            elif loadres:
                self.importres(_fileres=self.arg)
                self.sl = sb.SlabDB()
            elif '(' in str(arg):
                latlon = eval(self.arg)
                self.importosm(latlon=latlon, dist_m=self.dist_m, cart=self.bcartesian, typ=self.typ)
                self.loadosm = True
            else:
                self.importosm(address=self.arg, dist_m=self.dist_m, cart=self.bcartesian , typ=self.typ)
                self.loadosm = True

            if (not self.hasboundary) or (self.xlim != ()):
                self.boundary(xlim = self.xlim)

            self.subseg()
            self.updateshseg()

            try:
                self.geomfile()
            except:
                print("problem to construct geomfile")

            self.bconsistent = True
            if self.bcheck:
                self.bconsistent,dseg = self.check()

            if self.bconsistent:
                if self.bbuild:
                    self.build()
                    self.lbltg.append('s')
                    self.dumpw()
                elif self.bgraphs:
                    if os.path.splitext(self._filename)[1]=='.lay':
                        dirname = self._filename.replace('.lay','')
                    path = os.path.join(pro.basename,
                                        'struc',
                                        'graphml',
                                        dirname)
                    if os.path.exists(path):
                        self.dumpr('t')

                        if self._hash == self.Gt.nodes[0]['hash']:
                            self.dumpr('stvirw')
                            self.isbuilt = True
                            bbuild = False
                        else:
                            print(".lay file has changed you must rebuild the graphs")
                    else:
                        self.build()
                        self.lbltg.append('s')
                        self.dumpw()

    def __repr__(self):
        st = '\n'
        st = st + "----------------\n"
        home = os.path.expanduser('~')
        with open(os.path.join(home, '.pylayers'),'r') as f:
            paths = f.readlines()
        uporj = paths.index('project\n')
        project = paths[uporj+1]
        st = st + "Project : " + project+'\n'
        if hasattr(self, '_hash'):
            st = st + self._filename + ' : ' + self._hash + "\n"
        else:
            st = st + self._filename + "\n"


        if self.isbuilt:
            st = st + 'Built with : ' + self.Gt.node[0]['hash'] + "\n"
        st = st + 'Type : ' + self.typ+'\n'

        if self.display['overlay_file'] != '':
            filename = pyu.getlong(
                self.display['overlay_file'], os.path.join('struc', 'images'))
            st = st + "Image('" + filename + "')\n"
        st = st + "Coordinates : " + self.coordinates + "\n"
        if hasattr(self,'extent'):
            st = st + "----------------\n"
            st = st+ str(self.extent)+'\n'
        if hasattr(self,'extent_c'):
            st = st + "----------------\n"
            st = st+ str(self.extent_c)+'\n'
        if hasattr(self, 'Gs'):
            st = st + "----------------\n"
            st = st + "Gs : "+str(len(self.Gs.nodes()))+"("+str(self.Np)+'/'+str(self.Ns)+'/'+str(len(self.lsss))+') :'+str(len(self.Gs.edges()))+'\n'
        if hasattr(self,'Gt'):
            st = st + "Gt : "+str(len(self.Gt.nodes()))+' : '+str(len(self.Gt.edges()))+'\n'
        if hasattr(self,'Gv'):
            st = st + "Gv : "+str(len(self.Gv.nodes()))+' : '+str(len(self.Gv.edges()))+'\n'
        if hasattr(self,'Gi'):
            st = st + "Gi : "+str(len(self.Gi.nodes()))+' : '+str(len(self.Gi.edges()))+'\n'
        if hasattr(self,'Gr'):
            st = st + "Gr : "+str(len(self.Gr.nodes()))+' : '+str(len(self.Gr.edges()))+'\n'
        if hasattr(self,'Gw'):
            st = st + "Gw : "+str(len(self.Gw.nodes()))+' : '+str(len(self.Gw.edges()))+'\n'
        st = st + "----------------\n\n"
        if hasattr(self, 'degree'):
            for k in self.degree:
                if (k < 2) or (k > 3):
                    st = st + 'degree ' + \
                        str(k) + ' : ' + str(self.degree[k]) + "\n"
                else:
                    st = st + 'number of node points of degree ' + \
                        str(k) + ' : ' + str(len(self.degree[k])) + "\n"
        st = st + "\n"
        st = st + "xrange : " + str(self.ax[0:2]) + "\n"
        st = st + "yrange : " + str(self.ax[2:]) + "\n"
        if hasattr(self,'pg'):
            st = st + "center : " + "( %.2f,%.2f)" % (self.pg[0],self.pg[1]) + "\n"
        if hasattr(self,'radius'):
            st = st + "radius : %.2f " % self.radius + "\n"
        return(st)

    def __add__(self, other):
        """ addition

        One can add either a numpy array or an other layout

        """
        Ls = copy.deepcopy(self)
        if type(other) == np.ndarray:
            for k in Ls.Gs.pos:
                Ls.Gs.pos[k] = Ls.Gs.pos[k] + other[0:2]
        else:
            offp = -min(Ls.Gs.nodes())
            offs = max(Ls.Gs.nodes())
            other.offset_index(offp=offp, offs=offs)
            Ls.Gs.add_nodes_from(other.Gs.nodes(data=True))
            Ls.Gs.add_edges_from(other.Gs.edges(data=True))
            Ls.Gs.pos.update(other.Gs.pos)
            Ls.Np = Ls.Np + other.Np
            Ls.Ns = Ls.Ns + other.Ns
            Ls.Nss = Ls.Nss + other.Nss

        return(Ls)

    def __mul__(self, alpha):
        """ scale the layout

        other : scaling factor (np.array or int or float)

        Returns
        -------

        Ls : Layout
            scaled layout

        """
        Ls = copy.deepcopy(self)
        Gs = Ls.Gs
        if type(alpha) != np.ndarray:
            assert((type(alpha) == float) or (
                type(alpha) == int)), " not float"
            alpha = np.array([alpha, alpha, alpha])
        else:
            assert(len(alpha) == 3), " not 3D"

        x = np.array(list(Gs.pos.values()))[:, 0]
        x = x * alpha[0]

        y = np.array(list(Gs.pos.values()))[:, 1]
        y = y * alpha[1]

        xy = np.vstack((x, y)).T
        Ls.Gs.pos = dict(list(zip(list(Gs.pos.keys()), tuple(xy))))

        nseg = [x for x in Gs.nodes() if x > 0]
        for k in nseg:
            Ls.Gs.nodes[k]['z'] = tuple(
                (np.array(Ls.Gs.nodes[k]['z']) - self.zmin) * alpha[2] + self.zmin)
            if 'ss_z' in Ls.Gs.nodes[k]:
                Ls.Gs.nodes[k]['ss_z'] = list(
                    (np.array(Ls.Gs.nodes[k]['ss_z']) - self.zmin) * alpha[2] + self.zmin)

        Ls.g2npy()
        return Ls

    def switch(self):
        """ switch coordinates

        """
        if hasattr(self,'m'):
            if self.coordinates=='cart':
                for k in list(self.Gs.pos.keys()):
                    self.Gs.pos[k] = self.m( self.Gs.pos[k][0], self.Gs.pos[k][1], inverse=True)
                self.coordinates ='latlon'
            elif self.coordinates=='latlon':
                for k in list(self.Gs.pos.keys()):
                    self.Gs.pos[k] = self.m( self.Gs.pos[k][0], self.Gs.pos[k][1])
                self.coordinates ='cart'

            nodes = self.Gs.nodes()
            upnt = [n for n in nodes if n < 0]
            self.pt[0, :] = np.array([self.Gs.pos[k][0] for k in upnt])
            self.pt[1, :] = np.array([self.Gs.pos[k][1] for k in upnt])

    def _help(self):
        st = ''
        st = st + "\nUseful dictionnaries" + "\n----------------\n"
        if hasattr(self,'dca'):
            st = st + "dca {cycle : []} cycle with an airwall" +"\n"
        if hasattr(self,'di'):
            st = st + "di {interaction : [nstr,typi]}" +"\n"
        if hasattr(self,'sl'):
            st = st + "sl {slab name : slab dictionary}" +"\n"
        if hasattr(self,'name'):
            st = st + "name :  {slab :seglist} " +"\n"
        st = st + "\nUseful arrays"+"\n----------------\n"
        if hasattr(self,'pt'):
            st = st + "pt : numpy array of points " +"\n"
        if hasattr(self,'normal'):
            st = st + "normal : numpy array of normal " +"\n"
        if hasattr(self,'offset'):
            st = st + "offset : numpy array of offset " +"\n"
        if hasattr(self,'tsg'):
            st = st + "tsg : get segment index in Gs from tahe" +"\n"
        if hasattr(self,'isss'):
            st = st + "isss :  sub-segment index above Nsmax"+"\n"
        if hasattr(self,'tgs'):
            st = st + "tgs : get segment index in tahe from self.Gs" +"\n"
        if hasattr(self,'upnt'):
            st = st + "upnt : get point id index from self.pt"+"\n"

        st = st + "\nUseful Sparse arrays"+"\n----------------\n"
        if hasattr(self,'sgsg'):
            st = st + "sgsg : "+"get common point of 2 segment (usage self.sgsg[seg1,seg2] => return common point \n"
        if hasattr(self,'s2pc'):
            st = st + "s2pc : "+"from a Gs segment node to its 2 extremal points (tahe) coordinates\n"
        if hasattr(self,'s2pu'):
            st = st + "s2pc : "+"from a Gs segment node to its 2 extremal points (tahe) index\n"
        if hasattr(self,'p2pu'):
            st = st + "p2pc : "+"from a Gs point node to its coordinates\n"
        st = st + "\nUseful lists"+"\n----------------\n"
        if hasattr(self,'lsss'):
            st = st + "lsss : list of segments with sub-segment"+"\n"
        if hasattr(self,'sridess'):
            st = st + "stridess : stride to calculate the index of a subsegment" +"\n"
        if hasattr(self,'sla'):
            st = st + "sla : list of all slab names (Nsmax+Nss+1)" +"\n"
        if hasattr(self,'degree'):
            st = st + "degree : degree of nodes " +"\n"
        st = st + "\nUseful tip" + "\n----------------\n"
        st = st + "Point p in Gs => p_coord: Not implemented\n"
        st = st + "Segment s in Gs => s_ab coordinates \n"
        st = st + \
            "s -> u = self.tgs[s] -> v = self.tahe[:,u] -> s_ab = self.pt[:,v]\n\n"
        print(st)

    def ls(self, typ='lay'):
        """ list the available file in dirstruc

        Parameters
        ----------

        typ : string optional
            {'lay'|'osm'|'wrl'}

        Returns
        -------

        lfile_s : list
            sorted list of all the .str file of strdir

        """

        if typ == 'lay':
            pathname = os.path.join(pro.pstruc['DIRLAY'], '*.' + typ)
        if typ == 'osm':
            pathname = os.path.join(pro.pstruc['DIROSM'], '*.' + typ)
        if typ == 'wrl':
            pathname = os.path.join(pro.pstruc['DIRWRL'], '*.' + typ)

        lfile_l = glob.glob(os.path.join(pro.basename, pathname))
        lfile_s = []
        for fi in lfile_l:
            fis = pyu.getshort(fi)
            lfile_s.append(fis)
        lfile_s.sort()

        return lfile_s

    def offset_index(self, offp=0, offs=0):
        """ offset points and segment index

        Parameters
        ----------

        offp : offset points
        offs : offset segments

        """

        mapping = {}
        for n in self.Gs.nodes():
            if n < 0:
                mapping[n] = n - offp
            else:
                mapping[n] = n + offs
        nx.relabel_nodes(self.Gs, mapping, copy=False)


    def check(self, level=0, epsilon = 0.64):
        """ Check Layout consistency


        Parameters
        ----------

        level : int

        Returns
        -------

        consistent : Boolean
              True if consistent
        dseg : dictionnary of segments

        """

        bconsistent = True

        nodes = self.Gs.nodes()

        if len(nodes) > 0:

            useg = [ x for x in nodes if x > 0 ]
            upnt = [ x for x in nodes if x < 0 ]

            degseg = [nx.degree(self.Gs, x) for x in  useg ]

            assert(np.all(np.array(degseg) == 2))


            degpnt = [ nx.degree(self.Gs, x) for x in  upnt ]
            degmin = min(degpnt)
            degmax = max(degpnt)

            if (degmin <= 1):
                f, a = self.showG('s', aw=1)
                deg0 = [ x for x in upnt if nx.degree(self.Gs, x) == 0]
                deg1 = [ x for x in upnt if nx.degree(self.Gs, x) == 1]

                if len(deg0) > 0:
                    logger.critical( "It exists degree 0 points :  %r", deg0 )
                    f, a = self.pltvnodes(deg0, fig=f, ax=a)
                    bconsistent = False

                if len(deg1) > 0:
                    logger.critical( "It exists degree 1 points :  %r", deg1 )
                    f, a = self.pltvnodes(deg1, fig=f, ax=a)
                    bconsistent = False


            ke = list(self.Gs.pos.keys())
            lpos = list(self.Gs.pos.values())

            x = np.array([ pp[0] for pp in  lpos ] )
            y = np.array([ pp[1] for pp in  lpos ] )
            p = np.vstack((x, y))

            d1 = p - np.roll(p, 1, axis=1)
            sd1 = np.sum(np.abs(d1), axis=0)
            if not sd1.all() != 0:
                lu = np.where(sd1 == 0)[0]

                for u in lu:
                    if ke[u] < 0:
                        self.del_points(ke[u])

                nodes = self.Gs.nodes()
                upnt = [x for x in nodes if x < 0]

            dseg = {}
            if (self.typ == 'indoor') or (self.typ=='outdoor'):
                for s in useg:
                    n1, n2 = list(self.Gs.neighbors(s))
                    p1 = np.array(self.Gs.pos[n1])
                    p2 = np.array(self.Gs.pos[n2])
                    for n in upnt:
                        if (n1 != n) & (n2 != n):
                            p = np.array(self.Gs.pos[n])
                            if geu.isBetween(p1, p2, p,epsilon=epsilon):
                                if s in dseg:
                                    dseg[s].append(n)
                                else:
                                    dseg[s]=[n]
                                logger.critical("segment %d contains point %d", s, n)
                                bconsistent = False
                    if level > 0:
                        cycle = self.Gs.node[s]['ncycles']
                        if len(cycle) == 0:
                            logger.critical("segment %d has no cycle", s)
                        if len(cycle) == 3:
                            logger.critical(
                                "segment %d has cycle %s", s, str(cycle))

        P = np.array([self.Gs.pos[k] for k in upnt])
        similar = geu.check_point_unicity(P)

        if len(similar) != 0:
            logger.critical("points at index(es) %s in self.Gs.pos are similar", str(similar))
            bconsistent = False

        return bconsistent, dseg

    def clip(self, xmin, xmax, ymin, ymax):
        """ return the list of edges which cross or belong to the clipping zone

        Parameters
        ----------

        xmin : float
        xmax : float
        ymin : float
        ymax : float

        Returns
        -------

        seglist : list of segment number

        """

        p0 = self.pt[:, self.tahe[0, :]]
        p1 = self.pt[:, self.tahe[1, :]]

        maxx = np.maximum(p0[0, :], p1[0, :])
        maxy = np.maximum(p0[1, :], p1[1, :])

        minx = np.minimum(p0[0, :], p1[0, :])
        miny = np.minimum(p0[1, :], p1[1, :])

        nxp = np.nonzero(maxx < xmin)[0]
        nxm = np.nonzero(minx > xmax)[0]
        nyp = np.nonzero(maxy < ymin)[0]
        nym = np.nonzero(miny > ymax)[0]

        u = np.union1d(nxp, nxm)
        u = np.union1d(u, nyp)
        u = np.union1d(u, nym)

        iseg = np.arange(self.Ns)

        return np.setdiff1d(iseg, u)


    def check_Gi(self):

        for nit1 in self.Gi.nodes():
            if len(nit1)>1:
                cy1 = nit1[-1]
                for nint2 in list(self.Gi[nit1].keys()):
                    if len(nint2) > 1 :
                        assert nint2[1] == cy1

    def g2npy(self,verbose=False):
        """ conversion from graphs to numpy arrays

        Parameters
        ----------

        verbose : boolean

        """

        nodes = self.Gs.nodes()
        useg = [n for n in nodes if n >0]
        upnt = [n for n in nodes if n < 0]

        mno = max(nodes)

        for s in useg:
            lpts = [ x for x in self.Gs[s] ]
            assert(len(lpts)==2)
            assert(lpts[0]<0)
            assert(lpts[1]<0)
            a = [ x for x in self.Gs[lpts[0]]]
            b = [ x for x in self.Gs[lpts[1]]]

            nsa = np.setdiff1d(a,b)
            nsb = np.setdiff1d(b,a)
            u = np.hstack((nsa,nsb))

            npta = [lpts[0]]*len(nsa)
            nptb = [lpts[1]]*len(nsb)
            ns = np.hstack((npta,nptb))

        self.upnt = np.array((upnt))

        degseg = [ nx.degree(self.Gs,x) for x in useg ]

        assert(np.all(np.array(degseg) == 2))

        degpnt = np.array([nx.degree(self.Gs, x) for x in  upnt])

        lairwall = []

        if 'AIR' in self.name:
            lairwall += self.name['AIR']
        else:
            self.name['AIR'] = []

        if '_AIR' in self.name:
            lairwall += self.name['_AIR']
        else:
            self.name['_AIR'] = []

        def nairwall(nupt):
            lseg = self.Gs[nupt]
            n = 0
            for ns in lseg:
                if ns in lairwall:
                    n = n + 1
            return n

        nairwall = np.array([ nairwall(x) for x in  upnt])

        if verbose:
            print('buildging nairwall : Done')

        degpnt = degpnt - nairwall

        try:
            degmax = max(degpnt)
        except:
            degmax = 1

        self.degree = {}
        if verbose:
            print('Start node degree determination')
        for deg in range(degmax + 1):
            num = [ x for x in range(len(degpnt)) if degpnt[x] == deg ]
            npt = np.array([upnt[x] for x in num])
            self.degree[deg] = npt

        if verbose:
            print('Node degree determination  : Done')

        self.pt = np.array(np.zeros([2, len(upnt)]), dtype=float)
        self.tahe = np.array(np.zeros([2, len(useg)]), dtype=int)

        self.Np = len(upnt)
        self.Ns = len(useg)

        self.pt[0, :] = np.array([self.Gs.pos[k][0] for k in upnt])
        self.pt[1, :] = np.array([self.Gs.pos[k][1] for k in upnt])

        if verbose:
            print('pt in np.array  : Done')

        self.pg = np.sum(self.pt, axis=1) / np.shape(self.pt)[1]
        ptc = self.pt-self.pg[:,None]
        dptc = np.sqrt(np.sum(ptc*ptc,axis=0))
        self.radius  = dptc.max()
        self.pg = np.hstack((self.pg, 0.))

        if self.Ns>0:
            ntahe = np.array([ [n for n in self.Gs.neighbors(x) ]  for x in useg ])
            ntail = ntahe[:,0]
            nhead = ntahe[:,1]

            mlgsn = max(self.Gs.nodes())+1
            self.s2pu = sparse.lil_matrix((mlgsn,2),dtype='int')
            self.s2pu[useg,:] = ntahe
            self.s2pu = self.s2pu.tocsr()


        if self.Ns>0:
            aupnt = np.array(upnt)
            self.tahe[0, :] = np.array([np.where(aupnt==x)[0][0] for x in ntail ])
            self.tahe[1, :] = np.array([np.where(aupnt==x)[0][0] for x in nhead ])

        if verbose:
            print('tahe in numpy array : Done')
        Nsmax = 0
        self.tsg = np.array(useg)
        try:
            Nsmax = max(self.tsg)
        except:
            logger.warning("No segments in Layout yet")

        if Nsmax > 0:
            self.tgs = -np.ones(Nsmax + 1, dtype=int)
            rag = np.arange(len(useg))
            self.tgs[self.tsg] = rag

            X = np.vstack((self.pt[0, self.tahe[0, :]],
                           self.pt[0, self.tahe[1, :]]))
            Y = np.vstack((self.pt[1, self.tahe[0, :]],
                           self.pt[1, self.tahe[1, :]]))

            normx = Y[0, :] - Y[1, :]
            normy = X[1, :] - X[0, :]

            scale = np.sqrt(normx * normx + normy * normy)
            assert (scale.all() > 0)
            self.normal = np.vstack(
                (normx, normy, np.zeros(len(scale)))) / scale

            self.lsss = [x for x in useg if len(self.Gs.nodes[x]['iso']) > 0]

        if self.Ns >0:
            self.s2pc = sparse.lil_matrix((mlgsn,4))

            ptail = self.pt[:,self.tahe[0,:]]
            phead = self.pt[:,self.tahe[1,:]]
            A = np.vstack((ptail,phead)).T
            self.s2pc[self.tsg,:]=A

            self.s2pc = self.s2pc.tocsr()

            lheight = np.array([v[1] for v in
                        list(nx.get_node_attributes(self.Gs, 'z').values())
                        if v[1] < 2000 ])
            if len(lheight)>0:
                self.maxheight = np.max(lheight)
            else:
                self.maxheight = 3
            self.extrseg()

    def importshp(self, **kwargs):
        """ import layout from shape file

        Parameters
        ----------

        _fileshp :

        """
        defaults = {'pref': [np.array([25481100, 6676890]), np.array([60.2043716, 24.6591147])],
                    'dist_m': 250,
                    'latlon': True,
                    'bd': [24, 60, 25, 61],
                    }

        for k in defaults:
            if k not in kwargs:
                kwargs[k] = defaults[k]

        fileshp = pyu.getlong(kwargs['_fileshp'], os.path.join('struc', 'shp'))
        polys = shp.Reader(fileshp)
        verts = []
        for poly in polys.iterShapes():
            verts.append(poly.points)
        npt = -1
        ns = 0
        xmin = 1e16
        ymin = 1e16
        xmax = -1e16
        ymax = -1e16
        self.name['WALL'] = []
        for p in verts:
            v = np.array(p) - kwargs['pref'][0][None, :]
            nv = np.sqrt(np.sum(v * v, axis=1))
            if (nv < kwargs['dist_m']).any():
                npoint = len(p)
                for k, point in enumerate(p):
                    if k != (npoint - 1):
                        if k == 0:
                            np0 = npt
                        self.Gs.add_node(npt)
                        x = point[0]
                        y = point[1]
                        xmin = min(x, xmin)
                        xmax = max(x, xmax)
                        ymin = min(y, ymin)
                        ymax = max(y, ymax)
                        self.Gs.pos[npt] = (x, y)
                        npt = npt - 1
                    if (k > 0) & (k < npoint - 1):
                        ns = ns + 1
                        self.Gs.add_node(ns, name='WALL', z=[
                                         0, 10], offset=0, transition=False, connect=[npt + 1, npt + 2])
                        self.Gs.add_edge(npt + 1, ns)
                        self.Gs.add_edge(ns, npt + 2)
                        self.Gs.pos[ns] = tuple(
                            (np.array(self.Gs.pos[npt + 1]) + np.array(self.Gs.pos[npt + 2])) / 2.)
                    if k == npoint - 1:
                        ns = ns + 1
                        self.Gs.add_node(ns, name='WALL', z=[
                                         0, 10], offset=0, transition=False, connect=[np0, npt + 1])
                        self.Gs.add_edge(np0, ns)
                        self.Gs.add_edge(ns, npt + 1)
                        self.Gs.pos[ns] = tuple(
                            (np.array(self.Gs.pos[npt + 1]) + np.array(self.Gs.pos[np0])) / 2.)
        self.m = Basemap(llcrnrlon=kwargs['bd'][0], llcrnrlat=kwargs['bd'][1],
                         urcrnrlon=kwargs['bd'][2], urcrnrlat=kwargs['bd'][3],
                         resolution='i', projection='cass', lon_0=24.5, lat_0=60.5)

        if kwargs['latlon']:
            lat_ref = kwargs['pref'][1][0]
            lon_ref = kwargs['pref'][1][1]
            x_ref, y_ref = self.m(lon_ref, lat_ref)
            Dx = kwargs['pref'][0][0] - x_ref
            Dy = kwargs['pref'][0][1] - y_ref
            pos = np.array(list(self.Gs.pos.values()))
            for k, keys in enumerate(self.Gs.pos.keys()):
                self.Gs.pos[keys] = self.m( pos[k, 0] - Dx, pos[k, 1] - Dy, inverse=True)

            self.coordinates = 'latlon'

    def importres(self,_fileres,**kwargs):
        """ import res format

        col1 : x1 coordinates
        col2 : y1 coordinates
        col3 : x2 coordinates
        col4 : y2 coordinates
        col5 : building height
        col6 : building number
        col7 : building class
        col8 : ground height

        """
        fileres = pyu.getlong(_fileres, os.path.join('struc', 'res'))
        D  = np.fromfile(fileres,dtype='int',sep=' ')
        self.typ = 'outdoor'
        N1 = len(D)
        N2 = N1//8
        D = D.reshape(N2,8)
        lcoords = []
        lring = []
        zring = []
        bdg_old = 1
        for e in range(N2):
            p1 = ([D[e,0],D[e,1]])
            p2 = ([D[e,2],D[e,3]])
            z  = (D[e,7],D[e,4]+D[e,7])
            bdg =  D[e,5]
            bdc =  D[e,6]
            if (bdg_old-bdg)!=0:
                ring = sh.LinearRing(lcoords)
                poly = sh.Polygon(ring)
                if poly.area>0:
                    lring.append(ring)
                    zring.append(z)
                    lcoords = []
            bdg_old=bdg
            if p1 not in lcoords:
                lcoords.append(p1)
            if p2 not in lcoords:
                lcoords.append(p2)

        npt = 1

        for r1,z1 in zip(lring,zring):
            x,y = r1.xy

            for k2 in range(len(x)):
                new_pt = (x[k2],y[k2])
                kpos = list(self.Gs.pos.keys())
                vpos = list(self.Gs.pos.values())
                if new_pt not in vpos:
                    current_node_index = -npt
                    self.Gs.add_node(current_node_index)
                    self.Gs.pos[-npt] = new_pt
                    npt = npt + 1
                else:
                    u = [k for k in range(len(vpos)) if (vpos[k] == new_pt)]
                    current_node_index = kpos[u[0]]

                if k2>0:
                    ns = self.add_segment(current_node_index, previous_node_index, name='WALL', z=z1)
                else:
                    starting_node_index  =   current_node_index
                previous_node_index = current_node_index

    def dumpw(self):
        """ write a dump of given Graph in graphml format

        Notes
        -----

        't' : Gt
        'r' : Gr
        's' : Gs
        'v' : Gv
        'i' : Gi

        """
        if os.path.splitext(self._filename)[1]=='.ini':
            dirname = self._filename.replace('.ini','')
        if os.path.splitext(self._filename)[1]=='.lay':
            dirname = self._filename.replace('.lay','')
        path = os.path.join(pro.basename, 'struc', 'graphml', dirname)

        if not os.path.isdir(path):
            os.mkdir(path)
        for g in self.lbltg:
            try:
                gname = 'G' + g
                write_graphml(getattr(self, gname), os.path.join(
                    path, 'G' + g + '.graphml'), encoding='utf-8')
            except Exception as e:
                raise NameError(
                    'G' + g + ' graph cannot be saved, probably because it has not been built. Error: ' + str(e))
        
        if 't' in self.lbltg:
            if hasattr(self,'ddiff'):
                with open(os.path.join(path, 'ddiff.pkl'), 'wb') as f:
                    pickle.dump(self.ddiff, f)
            if hasattr(self,'lnss'):
                with open(os.path.join(path, 'lnss.pkl'), 'wb') as f:
                    pickle.dump(self.lnss, f)
        if hasattr(self,'dca'):
            with open(os.path.join(path, 'dca.pkl'), 'wb') as f:
                pickle.dump(self.dca, f)
        if hasattr(self, 'm'):
            with open(os.path.join(path, 'm.pkl'), 'wb') as f:
                pickle.dump(self.m, f)

    def dumpr(self, graphs='stvirw'):
        """ read graphs from graphml files

        Notes
        -----

        graph : string
            's' : Gv
            't' : Gt
            'r' : Gr
            'v' : Gv
            'i' : Gi

        .graphml files are stored under the struc/graphml directory of the project.

        """
        if os.path.splitext(self._filename)[1]=='.ini':
            dirname = self._filename.replace('.ini','')
        if os.path.splitext(self._filename)[1]=='.lay':
            dirname = self._filename.replace('.lay','')
        path = os.path.join(pro.basename, 'struc', 'graphml', dirname)
        
        for g in graphs:
            try:
                gname = 'G' + g
                filename = os.path.join(path, 'G' + g + '.graphml')
                G = read_graphml(filename, node_type=int)
                G = _convert_attributes(G)
                setattr(self, gname, G)
                self.lbltg.extend(g)
            except Exception as e:
                print(f"Warning: Unable to read graph G{g}. Error: {e}")

        if 's' in graphs:
            lseg = [x for x in self.Gs.nodes() if x > 0]
            for name in self.name:
                self.name[name] = [
                    x for x in lseg if self.Gs.nodes[x]['name'] == name]
            self.g2npy()

            filediff = os.path.join(path, 'ddiff.pkl')
            if os.path.isfile(filediff):
                with open(filediff, 'rb') as f:
                    ddiff = pickle.load(f)
                setattr(self, 'ddiff', ddiff)
            else:
                self.ddiff={}

            filelnss = os.path.join(path, 'lnss.pkl')
            if os.path.isfile(filelnss):
                with open(filelnss, 'rb') as f:
                    lnss = pickle.load(f)
                setattr(self, 'lnss', lnss)
            else :
                self.lnss=[]

        filedca = os.path.join(path, 'dca.pkl')
        if os.path.isfile(filedca):
            with open(filedca, 'rb') as f:
                dca = pickle.load(f)
            setattr(self, 'dca',dca)

        filem = os.path.join(path, 'm.pkl')
        if os.path.isfile(filem):
            with open(filem, 'rb') as f:
                setattr(self, 'm', pickle.load(f))