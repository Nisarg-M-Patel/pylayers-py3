#from pylayers.antprop.antenna import *
#from pylayers.antprop.antvsh import *
"""
.. currentmodule:: pylayers.antprop.antssh

.. autosummary::
    :members:

"""

import doctest
import os
import glob
from pylayers.antprop.spharm import *

import numpy as np
import scipy as sp
import pdb
import sys
import matplotlib.pyplot as plt
import doctest


def SSHFunc(L, theta,phi):
    """ ssh function

    Parameters
    ----------

    L : integer,
        spherical harmonics order
    theta: numpy array (1,nth)
    phi: numpy array (1,nph)

    Returns
    -------

    Y : np.array
        ((1+L)*(2+L)/2,nth*nph)
    indx : np.array


    Notes
    -----

    Compute the spherical harmonic functions for the order L
    return a spherical matrix ((1+L)*(2+L)/2,nth*nph) and the index (l,m) of the shperical harmonics

    """

    l = np.arange(0,1+L).reshape(1,(1+L))
    m = np.arange(0,1+L).reshape(((1+L),1))
    # normalize the associated Legendre polynoms
    NRM = np.sqrt((2*l+1)*factorial(l-abs(m))/(4*np.pi*factorial(l+abs(m))))
    NRM = NRM.reshape((1+L,1+L,1))
    # compute the associated Legendre polynoms part Plm(cos(theta))
    ll = l.reshape(1,(1+L),1)
    mm = m.reshape(((1+L),1,1))
    x  = np.cos(theta).reshape((1,1, len(theta)))
    PLM = sp.special.lpmv(mm,ll,x)
    # Normalize
    NPLM = NRM*PLM
    NPLM = NPLM.reshape((1+L,1+L,len(theta),1))
    # compute the exp(j*m*phi) part
    PHI = phi.reshape((1,len(phi)))
    mm = m.reshape(((1+L),1))
    EXP = np.exp(1j*mm*PHI)
    EXP = EXP.reshape((1+L,1,1,len(phi)))
    # Compute Y : the spherical harmonics matrix and reshaping it
    Yi= NPLM*EXP
    Yi = Yi.reshape(((1+L)**2,len(theta)*len(phi)))
    #~ Y = Yi
    nzero_rows = Yi.any(axis = 1)
    Y  = Yi[nzero_rows] # eliminating the undefined functions (Y01)
    ll = (l*np.ones((1+L,1))).reshape(((1+L)**2))
    mm = (m*np.ones((1,1+L))).reshape(((1+L)**2))
    # spherical harmonics index
    #~ indx = np.array([ll[nzero_rows],mm[nzero_rows]]).T
    indx = np.array([ll[nzero_rows],mm[nzero_rows]]).T
    Y2 = ((-1)**indx[1+L:,1]).reshape((len(indx[1+L:,1]),1))*np.conj(Y[1+L:,:])
    Y = np.append(Y,Y2, axis  = 0)
    indx2 =  np.array([indx[1+L:,0],(-1)*indx[1+L:,1]]).T
    indx = np.append(indx,indx2, axis = 0)
    return Y,  indx

def SSHFunc2(L, theta,phi):
    """ ssh function version 2

    Parameters
    ----------

    L : integer,
        spherical harmonics order
    theta: numpy array(1,ndir)
    phi: numpy array(1,ndir)

    Notes
    -----

    theta and phi should have the same dimensions which represents the rays
    Compute the spherical harmonic functions for the order L
    return a spherical matrix ((1+L)*(2+L)/2,ndir) and the index (l,m) of the shperical harmonics

    """

    nray = len(theta)
    l = np.arange(0,1+L).reshape(1,(1+L))
    m = np.arange(0,1+L).reshape(((1+L),1))
    # normalize the associated legendre polynoms
    NRM = np.sqrt((2*l+1)*factorial(l-abs(m))/(4*np.pi*factorial(l+abs(m))))
    NRM = NRM.reshape((1+L,1+L,1))
    # compute the associated legendre polynoms part Plm(cos(theta))
    ll = l.reshape(1,(1+L),1)
    mm = m.reshape(((1+L),1,1))
    x  = np.cos(theta).reshape((1,1, nray))
    PLM = sp.special.lpmv(mm,ll,x)
    # Normalize
    NPLM = NRM*PLM
    NPLM = NPLM.reshape((1+L,1+L,nray))
    # compute the exp(j*m*phi) part
    PHI = phi.reshape((1,nray))
    mm = m.reshape(((1+L),1))
    EXP = np.exp(1j*mm*PHI)
    EXP = EXP.reshape((1+L,1,nray))
    # Compute Y : the spherical harmonics matrix and reshaping it
    Yi= NPLM*EXP
    Yi = Yi.reshape(((1+L)**2,nray))
    #~ Y = Yi
    nzero_rows = Yi.any(axis = 1)
    Y = Yi[nzero_rows] # eliminating the non defined functions (Y01)
    ll = (l*np.ones((1+L,1))).reshape(((1+L)**2))
    mm = (m*np.ones((1,1+L))).reshape(((1+L)**2))
    # spherical harmonics index
    #~ indx = np.array([ll[nzero_rows],mm[nzero_rows]]).T
    indx = np.array([ll[nzero_rows],mm[nzero_rows]]).T
    Y2 = ((-1)**indx[1+L:,1]).reshape((len(indx[1+L:,1]),1))*np.conj(Y[1+L:,:])
    Y = np.append(Y,Y2, axis  = 0)
    indx2 =  np.array([indx[1+L:,0],(-1)*indx[1+L:,1]]).T
    indx = np.append(indx,indx2, axis = 0)
    return Y, indx

def SphereToCart (theta, phi, eth, eph, bfreq ):
    """ Spherical to Cartesian

    Parameters
    ----------

    theta :
    phi   :
    eth   :
    eph   :
    bfreq: boolean
        indicate if the conversion is done for all frequencies or only one.

    """

    if bfreq == False:
        PHI = phi.reshape((1,len(phi)))
        THETA = theta.reshape((len(theta),1))
        ec = ndarray(shape = (3, len(theta),len(phi)) , dtype  = complex  )

    else:
        PHI = phi.reshape((1,len(phi),1))
        THETA = theta.reshape((len(theta),1,1))
        ec = np.ndarray(shape = (3, len(theta),len(phi),eth.shape[-1] ) , dtype  = complex  )


    ec[0] = np.cos(THETA)*np.cos(PHI)*eth -np.sin(PHI)*eph
    ec[1] = np.cos(THETA)*np.sin(PHI)*eth +np.cos(PHI)*eph
    ec[2] = -np.sin(THETA)*eth

    return ec

def CartToSphere (theta, phi,ex,ey,ez, bfreq=True, pattern = True):
    """ Convert from Cartesian to Spherical

    Parameters
    ----------
    theta
    phi
    ex
    ey
    ez
    bfreq  : boolean
    pattern : boolean

    Convert from cartesian to spherical  coordinates
    bfreq : boolean parameter to indicate if the conversion is done for all frequencies of only one.
    """

    nray = len(theta)

    if bfreq == False:
        es = np.ndarray(shape = (2, nray) , dtype  = complex  )
    else:
        es = np.ndarray(shape = (2, ex.shape[0], nray) , dtype  = complex  )

    es[0] = np.cos(theta)*np.cos(phi)*ex + np.cos(theta)*np.sin(phi)*ey -np.sin(theta)*ez
    es[1] = -np.sin(phi)*ex +np.cos(phi)*ey

    return es[0],es[1]


def ssh(A,L= 20,dsf=1):
    """

    Parameters
    ----------

    A   :  antenna
    dsf :  int
        down sampling factor  'default 1'

    Notes 
    -----

    This function calculates the Scalar Spherical Harmonics coefficients

        m : phi    longitude
        l : theta  latitude

    Antenna pattern are stored       (f theta phi)
    Coeff are stored with this order (f , l , m )

    """

    th = A.theta[::dsf]
    ph = A.phi[::dsf]
    nth = len(th)
    nph = len(ph)
    nf = A.nf

    if (nph % 2) == 1:
        mdab = min(nth, (nph + 1) / 2)
    else:
        mdab = min(nth, nph / 2)

    ndab = nth


    Etheta  =  A.Ft[::dsf,::dsf,:]
    Ephi    =  A.Fp[::dsf,::dsf,:]

    # compute the spherical harmonics functions at the order L
    Y,ssh_index  = SSHFunc(L,th,ph)
    # Compute the pseudo inverse of Y
    Ypinv = sp.linalg.pinv(Y)

    # convert the field from spherical to cartesian coordinates system
    Ex,Ey,Ez = SphereToCart (th, ph, Etheta, Ephi, True)
    #
    Ex = Ex.reshape((nf,nth*nph))
    Ey = Ey.reshape((nf,nth*nph))
    Ez = Ez.reshape((nf,nth*nph))

    cx  =  np.dot(Ex,Ypinv)
    cy  =  np.dot(Ey,Ypinv)
    cz  =  np.dot(Ez,Ypinv)
    lmax = L

    Cx = SCoeff(typ='s2',fmin=A.fGHz[0],fmax=A.fGHz[-1],lmax=lmax,data=cx,ind=ssh_index)
    Cy = SCoeff(typ='s2',fmin=A.fGHz[0],fmax=A.fGHz[-1],lmax=lmax,data=cy,ind=ssh_index)
    Cz = SCoeff(typ='s2',fmin=A.fGHz[0],fmax=A.fGHz[-1],lmax=lmax,data=cz,ind=ssh_index)

    A.S = SSHCoeff(Cx,Cy,Cz)


    return(A)

def sshs(G,fGHz,th,ph,L= 20):
    """scalar spherical harmonics transform

    Parameters
    ----------

    G    :  antenna gain (f,th,phi)
    fGHz : np.array
    th   : np.array
    ph   : np.array

    Notes
    -----

    This function calculates the Scalar Spherical Harmonics coefficients

        m : phi    longitude
        l : theta  latitude

    Antenna pattern are stored       (f theta phi)
    Coeff are stored with this order (f , l , m )

    """

    th = A.theta[::dsf]
    ph = A.phi[::dsf]
    nth = len(th)
    nph = len(ph)
    nf = A.nf

    if (nph % 2) == 1:
        mdab = min(nth, (nph + 1) / 2)
    else:
        mdab = min(nth, nph / 2)

    ndab = nth


    #Etheta  =  A.Ft[::dsf,::dsf,:]
    #Ephi    =  A.Fp[::dsf,::dsf,:]

    # compute the spherical harmonics functions at the order L
    Y,ssh_index  = SSHFunc(L,th,ph)
    # Compute the pseudo inverse of Y
    Ypinv = sp.linalg.pinv(Y)

    # convert the field from spherical to cartesian coordinates system
    #Ex,Ey,Ez = SphereToCart (th, ph, Etheta, Ephi, True)
    #
    G = G.reshape((nf,nth*nph))

    cg  =  np.dot(G,Ypinv)
    lmax = L

    Cg = SCoeff(typ='s2',fmin=fGHz[0],fmax=fGHz[-1],lmax=lmax,data=cg,ind=ssh_index)

    return(Cg)


if (__name__=="__main__"):
    doctest.testmod()

