"""
Modern replacement for deprecated mpl_toolkits.basemap using pyproj
Provides API compatibility for PyLayers migration
"""
import pyproj
import numpy as np

class Basemap:
    """
    Modern Basemap replacement using pyproj for coordinate transformations
    
    Supports the Cassini projection used throughout PyLayers
    """
    
    def __init__(self, llcrnrlon, llcrnrlat, urcrnrlon, urcrnrlat, 
                 projection='cass', lon_0=None, lat_0=None, resolution='i', **kwargs):
        """
        Initialize coordinate transformer
        
        Parameters
        ----------
        llcrnrlon : float
            Lower left corner longitude
        llcrnrlat : float
            Lower left corner latitude
        urcrnrlon : float
            Upper right corner longitude
        urcrnrlat : float
            Upper right corner latitude
        projection : str
            Map projection (only 'cass' supported for now)
        lon_0 : float
            Central longitude
        lat_0 : float
            Central latitude
        resolution : str
            Map resolution (ignored, for API compatibility)
        """
        
        self.llcrnrlon = llcrnrlon
        self.llcrnrlat = llcrnrlat
        self.urcrnrlon = urcrnrlon
        self.urcrnrlat = urcrnrlat
        self.projection = projection
        
        # Set central meridian and parallel
        if lon_0 is None:
            self.lon_0 = (llcrnrlon + urcrnrlon) / 2.0
        else:
            self.lon_0 = lon_0
            
        if lat_0 is None:
            self.lat_0 = (llcrnrlat + urcrnrlat) / 2.0
        else:
            self.lat_0 = lat_0
        
        # Create pyproj transformer for Cassini projection
        if projection == 'cass':
            # Define Cassini projection with pyproj
            proj_string = f"+proj=cass +lat_0={self.lat_0} +lon_0={self.lon_0} +x_0=0 +y_0=0 +datum=WGS84 +units=m +no_defs"
            
            # Create transformers
            self.proj_crs = pyproj.CRS.from_proj4(proj_string)
            self.geo_crs = pyproj.CRS.from_epsg(4326)  # WGS84
            
            # Forward transformer: lat/lon -> x/y
            self.transformer_fwd = pyproj.Transformer.from_crs(
                self.geo_crs, self.proj_crs, always_xy=True
            )
            
            # Inverse transformer: x/y -> lat/lon  
            self.transformer_inv = pyproj.Transformer.from_crs(
                self.proj_crs, self.geo_crs, always_xy=True
            )
        else:
            raise NotImplementedError(f"Projection '{projection}' not implemented. Only 'cass' is supported.")
    
    def __call__(self, lon, lat, inverse=False):
        """
        Transform coordinates
        
        Parameters
        ----------
        lon : float or array-like
            Longitude (or x if inverse=True)
        lat : float or array-like  
            Latitude (or y if inverse=True)
        inverse : bool
            If False: transform lon/lat -> x/y
            If True: transform x/y -> lon/lat
            
        Returns
        -------
        x, y : float or array-like
            Transformed coordinates
        """
        
        # Convert to numpy arrays for consistent handling
        is_scalar = np.isscalar(lon) and np.isscalar(lat)
        lon = np.atleast_1d(lon)
        lat = np.atleast_1d(lat)
        
        if inverse:
            # Transform x/y -> lon/lat
            x, y = self.transformer_inv.transform(lon, lat)
        else:
            # Transform lon/lat -> x/y
            x, y = self.transformer_fwd.transform(lon, lat)
        
        # Return scalars if input was scalar
        if is_scalar:
            return float(x[0]), float(y[0])
        else:
            return x, y
    
    # Additional properties for API compatibility
    @property
    def llcrnrx(self):
        """Lower left corner x coordinate"""
        x, y = self(self.llcrnrlon, self.llcrnrlat)
        return x
    
    @property
    def llcrnry(self):
        """Lower left corner y coordinate"""
        x, y = self(self.llcrnrlon, self.llcrnrlat)
        return y
        
    @property
    def urcrnrx(self):
        """Upper right corner x coordinate"""
        x, y = self(self.urcrnrlon, self.urcrnrlat)
        return x
        
    @property
    def urcrnry(self):
        """Upper right corner y coordinate"""
        x, y = self(self.urcrnrlon, self.urcrnrlat)
        return y