#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
.. currentmodule:: pylayers.antprop.srtm

.. autosummary::

"""

import doctest
import os
import glob
# Pylint: Disable name warningsos.path.join(self.directory,continent)
# pylint: disable-msg=C0103

"""Load and process SRTM data."""

#import xml.dom.minidom
from html.parser import HTMLParser
import ftplib
import sys
if sys.version_info.major==2:
    import urllib.request, urllib.error, urllib.parse
    _PY3=False
else:
    from urllib.request import urlopen
    _PY3=True
import re
import pickle
import os.path
import os
import zipfile
import array
import math
import pdb
import matplotlib.pyplot as plt
import numpy as np

class NoSuchTileError(Exception):
    """Raised when there is no tile for a region."""
    def __init__(self, lat, lon):
        Exception.__init__()
        self.lat = lat
        self.lon = lon

    def __str__(self):
        return "No SRTM tile for %d, %d available!" % (self.lat, self .lon)

class WrongTileError(Exception):
    """Raised when the value of a pixel outside the tile area is reque sted."""
    def __init__(self, tile_lat, tile_lon, req_lat, req_lon):
        Exception.__init__()
        self.tile_lat = tile_lat
        self.tile_lon = tile_lon
        self.req_lat = req_lat
        self.req_lon = req_lon

    def __str__(self):
        return "SRTM tile for %d, %d does not contain data for %d, %d!" % (
            self.tile_lat, self.tile_lon, self.req_lat, self.req_lon)

class InvalidTileError(Exception):
    """Raised when the SRTM tile file contains invalid data."""
    def __init__(self, lat, lon):
        Exception.__init__()
        self.lat = lat
        self.lon = lon

    def __str__(self):
        return "SRTM tile for %d, %d is invalid!" % (self.lat, self.lon)

class SRTMDownloader:
    """Automatically download SRTM tiles."""
    def __init__(self, server="dds.cr.usgs.gov",
                 directory=os.path.join('srtm','version2_1','SRTM3'),
                 cachedir="cache",
                 protocol="http"):
        self.protocol = protocol
        self.server = server
        self.directory = directory
        self.cachedir = cachedir
        print("SRTMDownloader - server= %s, directory=%s." % \
              (self.server, self.directory))
        if not os.path.exists(cachedir):
            os.mkdir(cachedir)
        self.filelist = {}
        self.filename_regex = re.compile(r"([NS])(\d{2})([EW])(\d{3})\.hgt\.zip")
        self.filelist_file = os.path.join(self.cachedir,"filelist_python")
        self.ftpfile = None
        self.ftp_bytes_transfered = 0

    def loadFileList(self):
        """Load a previously created file list or create a new one if none is
            available."""
        try:
            data = open(self.filelist_file, 'rb')
        except IOError:
            print("No cached file list. Creating new one!")
            self.createFileList()
            return
        try:
            self.filelist = pickle.load(data)
        except:
            print("Unknown error loading cached file list. Creating new one!")
            self.createFileList()

    def createFileList(self):
        """SRTM data is split into different directories, get a list of all of
            them and create a dictionary for easy lookup."""
        if self.protocol == "ftp":
            ftp = ftplib.FTP(self.server)
            try:
                ftp.login()
                ftp.cwd(self.directory)
                continents = ftp.nlst()
                for continent in continents:
                    print("Downloading file list for", continent)
                    ftp.cwd(os.path.join(self.directory,continent))
                    files = ftp.nlst()
                    for filename in files:
                        s.path.join(self.directory,continent)
                        self.filelist[self.parseFilename(filename)] = (
                                continent, filename)
            finally:
                ftp.close()
            # Add meta info
            self.filelist["server"] = self.server
            self.filelist["directory"] = self.directory
            with open(self.filelist_file , 'wb') as output:
                pickle.dump(self.filelist, output)
        else:
            self.createFileListHTTP()

    def createFileListHTTP(self):
        """Create a list of the available SRTM files on the server using
        HTTP file transfer protocol (rather than ftp).
        30may2010  GJ ORIGINAL VERSION
        """
        print("createFileListHTTP")
        if _PY3:
            r1 = urlopen('http://'+self.server+'/'+self.directory)
        else:
            conn = urllib.request.Request('http://'+self.server+'/'+self.directory)
            r1 = urllib.request.urlopen(conn)
        #if r1.status==200:
        #    print "status200 received ok"
        #else:
        #    print "oh no = status=%d %s" \
        #          % (r1.status,r1.reason)
        data = r1.read()
        if isinstance(data,bytes):
            data=data.decode()
        parser = parseHTMLDirectoryListing()
        parser.feed(data)
        continents = parser.getDirListing()
        print(continents)

        for continent in continents:
            print("Downloading file list for", continent)
            if _PY3:
                r1 = urlopen('http://'+self.server+'/'+self.directory+'/'+continent)
            else:
                conn = urllib.request.Request('http://'+self.server+'/'+self.directory+'/'+continent)
                r1 = urllib.request.urlopen(conn)
            data = r1.read()
            if isinstance(data,bytes):
                data=data.decode()
            parser = parseHTMLDirectoryListing()
            parser.feed(data)
            files = parser.getDirListing()

            for filename in files:
                self.filelist[self.parseFilename(filename)] = (
                            continent, filename)

            #print self.filelist
        # Add meta info
        self.filelist["server"] = self.server
        self.filelist["directory"] = self.directory
        with open(self.filelist_file , 'wb') as output:
            pickle.dump(self.filelist, output)



    def parseFilename(self, filename):
        """Get lat/lon values from filename."""
        match = self.filename_regex.match(filename)
        if match is None:
            # TODO?: Raise exception?
            print("Filename", filename, "unrecognized!")
            return None
        lat = int(match.group(2))
        lon = int(match.group(4))
        if match.group(1) == "S":
            lat = -lat
        if match.group(3) == "W":
            lon = -lon
        return lat, lon

    def getTile(self, lat, lon):
        """Get a SRTM tile object. This function can return either an SRTM1 or
            SRTM3 object depending on what is available, however currently it
            only returns SRTM3 objects."""
        try:
            continent, filename = self.filelist[(int(lat), int(lon))]
            print(filename)
        except KeyError:
            raise NoSuchTileError(lat, lon)
        if not os.path.exists(os.path.join(self.cachedir,filename)):
            self.downloadTile(continent, filename)
        # TODO: Currently we create a new tile object each time.
        # Caching is required for improved performance.
        return SRTMTile(os.path.join(self.cachedir,filename), int(lat), int(lon))

    def downloadTile(self, continent, filename):
        """Download a tile from NASA's server and store it in the cache."""
        if self.protocol=="ftp":
            ftp = ftplib.FTP(self.server)
            try:
                ftp.login()
                ftp.cwd(os.path.join(self.directory,continent))
                # WARNING: This is not thread safe
                self.ftpfile = open(os.path.join(self.cachedir,filename), 'wb')
                self.ftp_bytes_transfered = 0
                print("")
                try:
                    ftp.retrbinary("RETR "+filename, self.ftpCallback)
                finally:
                    self.ftpfile.close()
                    self.ftpfile = None
            finally:
                ftp.close()
        else:
            #Use HTTP
            if _PY3:
                r1 = urlopen('http://'+self.server+'/'+self.directory+'/'+continent+'/'+filename)
            else:

                conn = urllib.request.Request('http://'+self.server+'/'+self.directory+'/'+continent+'/'+filename)
                r1 = urllib.request.urlopen(conn)
            data = r1.read()
            self.ftpfile = open(os.path.join(self.cachedir,filename), 'wb')
            self.ftpfile.write(data)
            self.ftpfile.close()
            self.ftpfile = None


    def ftpCallback(self, data):
        """Called by ftplib when some bytes have been received."""
        self.ftpfile.write(data)
        self.ftp_bytes_transfered += len(data)
        print("\r%d bytes transfered" % self.ftp_bytes_transfered,)

class SRTMTile:
    """Base class for all SRTM tiles.
        Each SRTM tile is size x size pixels big and contains
        data for the area from (lat, lon) to (lat+1, lon+1) inclusive.
        This means there is a 1 pixel overlap between tiles. This makes it
        easier for as to interpolate the value, because for every point we
        only have to look at a single tile.
        """
    def __init__(self, f, lat, lon):
        zipf = zipfile.ZipFile(f, 'r')
        names = zipf.namelist()
        if len(names) != 1:
            raise InvalidTileError(lat, lon)
        data = zipf.read(names[0])
        self.size = int(math.sqrt(len(data)/2)) # 2 bytes per sample
        # Currently only SRTM1/3 is supported
        if self.size not in (1201, 3601):
            raise InvalidTileError(lat, lon)
        self.data = array.array('h', data)
        self.data.byteswap()
        if len(self.data) != self.size * self.size:
            raise InvalidTileError(lat, lon)
        self.lat = lat
        self.lon = lon

    @staticmethod
    def _avg(value1, value2, weight):
        """Returns the weighted average of two values and handles the case where
            one value is None. If both values are None, None is returned.
        """
        if value1 is None:
            return value2
        if value2 is None:
            return value1
        return value2 * weight + value1 * (1 - weight)

    def calcOffset(self, x, y):
        """Calculate offset into data array. Only uses to test correctness
            of the formula."""
        # Datalayout
        # X = longitude
        # Y = latitude
        # Sample for size 1201x1201
        #  (   0/1200)     (   1/1200)  ...    (1199/1200)    (1200/1200)
        #  (   0/1199)     (   1/1199)  ...    (1199/1199)    (1200/1199)
        #       ...            ...                 ...             ...
        #  (   0/   1)     (   1/   1)  ...    (1199/   1)    (1200/   1)
        #  (   0/   0)     (   1/   0)  ...    (1199/   0)    (1200/   0)
        #  Some offsets:
        #  (0/1200)     0
        #  (1200/1200)  1200
        #  (0/1199)     1201
        #  (1200/1199)  2401
        #  (0/0)        1201*1200
        #  (1200/0)     1201*1201-1
        return x + self.size * (self.size - y - 1)

    def getPixelValue(self, x, y):
        """Get the value of a pixel from the data, handling voids in the
            SRTM data."""
        assert x < self.size, "x: %d<%d" % (x, self.size)
        assert y < self.size, "y: %d<%d" % (y, self.size)
        # Same as calcOffset, inlined for performance reasons
        offset = x + self.size * (self.size - y - 1)
        #print offset
        value = self.data[offset]
        if value == -32768:
            return None # -32768 is a special value for areas with no data
        return value
        

    def getAltitudeFromLatLon(self, lat, lon):
        """Get the altitude of a lat lon pair, using the four neighbouring
            pixels for interpolation.
        """
        # print "-----\nFromLatLon", lon, lat
        lat -= self.lat
        lon -= self.lon
        # print "lon, lat", lon, lat
        if lat < 0.0 or lat >= 1.0 or lon < 0.0 or lon >= 1.0:
            raise WrongTileError(self.lat, self.lon, self.lat+lat, self.lon+lon)
        x = lon * (self.size - 1)
        y = lat * (self.size - 1)
        # print "x,y", x, y
        x_int = int(x)
        x_frac = x - int(x)
        y_int = int(y)
        y_frac = y - int(y)
        # print "frac", x_int, x_frac, y_int, y_frac
        value00 = self.getPixelValue(x_int, y_int)
        value10 = self.getPixelValue(x_int+1, y_int)
        value01 = self.getPixelValue(x_int, y_int+1)
        value11 = self.getPixelValue(x_int+1, y_int+1)
        value1 = self._avg(value00, value10, x_frac)
        value2 = self._avg(value01, value11, x_frac)
        value  = self._avg(value1,  value2, y_frac)
        # print "%4d %4d | %4d\n%4d %4d | %4d\n-------------\n%4d" % (
        #        value00, value10, value1, value01, value11, value2, value)
        return value



class parseHTMLDirectoryListing(HTMLParser):

    def __init__(self):
        #print "parseHTMLDirectoryListing.__init__"
        HTMLParser.__init__(self)
        self.title="Undefined"
        self.isDirListing = False
        self.dirList=[]
        self.inTitle = False
        self.inHyperLink = False
        self.currAttrs=""
        self.currHref=""

    def handle_starttag(self, tag, attrs):
        #print "Encountered the beginning of a %s tag" % tag
        if tag=="title":
            self.inTitle = True
        if tag == "a":
            self.inHyperLink = True
            self.currAttrs=attrs
            for attr in attrs:
                if attr[0]=='href':
                    self.currHref = attr[1]


    def handle_endtag(self, tag):
        #print "Encountered the end of a %s tag" % tag
        if tag=="title":
            self.inTitle = False
        if tag == "a":
            # This is to avoid us adding the parent directory to the list.
            if self.currHref!="":
                self.dirList.append(self.currHref)
            self.currAttrs=""
            self.currHref=""
            self.inHyperLink = False

    def handle_data(self,data):
        if self.inTitle:
            self.title = data
            print("title=%s" % data)
            if "Index of" in self.title:
                #print "it is an index!!!!"
                self.isDirListing = True
        if self.inHyperLink:
            # We do not include parent directory in listing.
            if  "Parent Directory" in data:
                self.currHref=""

    def getDirListing(self):
        return self.dirList

#DEBUG ONLY
if __name__ == '__main__':
    downloader = SRTMDownloader()
    downloader.loadFileList()
    latitude = input("latitude : ")
    longitude = input("longitude : ")
    tile = downloader.getTile(latitude,longitude)
    I = np.array(tile.data).reshape(1201,1201)
    n = np.where(I<0)
    I[n]=0
    plt.imshow(I)
    plt.colorbar()
    plt.show()
    #tile.getAltitudeFromLatLon(49.1234, 12.56789)
