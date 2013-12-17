module Modules.Imports where


module X where

  module ImportExample where

    data Bool : Set where
      false true : Bool

  x = ImportExample.true

module X́ where

  import ImportExample -- this module exists outside of this file

  x = ImportExample.true


module X″ where

  module ImportExample where

    data Bool : Set where
      false true : Bool

  x = ImportExample.true

module X‴ where

  import Modules.ImportExample  -- this module exists outside of this file

  x = Modules.ImportExample.true


module X⁗ where

  import Modules.ImportExample as ImportExample

  x = ImportExample.true -- jump to definition by C-. and come back here by C-* , please check original module name

