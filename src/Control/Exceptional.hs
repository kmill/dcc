{-|

  The 'Control.Exceptional' library contains two types, 'Exceptional'
  and 'ExceptionalT', which are essentially just 'Either' and
  'EitherT'.  Actually, the functionality is identical.  For that
  reason, one may ask why 'Control.Exceptional' came into existence.
  A possible reason is that the names 'Success' and 'Exception' are
  better than 'Right' and 'Left'.  The actual reason is that some
  versions of 'Prelude' might not have an instance @Monad (Either e)@,
  but some might, so we can't just add such an instance ourselves.

-}
module Control.Exceptional
    (
     Exceptional(..), throwE, catchE,
     ExceptionalT(..), throwT, catchT
    ) where

import Control.Applicative
import Control.Monad.Trans

data Exceptional e a = Success a -- ^ Essentially 'Right'
                     | Exception e -- ^ Essentially 'Left'
                       deriving (Show)

instance Monad (Exceptional e) where
    return = Success
    (Success x) >>= f    = f x
    (Exception x) >>= _  = Exception x

instance Functor (Exceptional e) where
    fmap f (Success x) = Success $ f x
    fmap _ (Exception x) = (Exception x)

instance Applicative (Exceptional e) where
    pure = Success
    a <*> b = do x <- a
                 y <- b
                 return $ x y

-- | This is just the 'Exception' constructor.
throwE :: a -> Exceptional a b
throwE = Exception

-- | This could have easily have been of type @Exceptional a b -> (a
-- -> b) -> Exceptional a b@ or @Exceptional a b -> (a -> Exceptional
-- a b) -> Exceptional a b@ (the latter being nice as far as symmetry
-- with @>>=@ goes), but the use case of recovering from a possible
-- exception informed the decision.
catchE :: Exceptional a b -> (a -> b) -> b
catchE (Success x) _ = x
catchE (Exception x) f = f x

-- | This is a monad transformer which inserts an 'Exceptional' monad.
newtype ExceptionalT e m a = ExceptionalT { runExceptionalT :: m (Exceptional e a) }

instance Monad m => Monad (ExceptionalT e m) where
    return   = ExceptionalT . return . return
    m >>= f  = ExceptionalT $ do
                 ea <- runExceptionalT m
                 case ea of
                   Exception l -> return $ Exception l
                   Success r -> runExceptionalT $ f r
instance Monad m => Functor (ExceptionalT e m) where
    fmap f ma = ExceptionalT $ do
                  a <- runExceptionalT ma
                  return $ fmap f a
                   
instance Monad m => Applicative (ExceptionalT e m) where
    pure = ExceptionalT . return . return
    ma <*> mb = ExceptionalT $ do
                  a <- runExceptionalT ma
                  b <- runExceptionalT mb
                  return $ a <*> b

instance MonadTrans (ExceptionalT e) where
    lift m = ExceptionalT $ m >>= (return . return)

-- | Lifts 'throwE' into the monad transformer.
throwT :: Monad m => e -> ExceptionalT e m a
throwT = ExceptionalT . return . throwE

-- | Lifts 'catchE' into the monad transformer.
catchT :: Monad m => ExceptionalT e m a -> (e -> a) -> m a
catchT ext f = runExceptionalT ext >>= (return . (flip catchE f))
