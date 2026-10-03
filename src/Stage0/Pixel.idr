module Stage0.Pixel

%default total

public export
data Metric = Blue | Red | Green

public export
Eq Metric where
  Blue == Blue = True
  Red == Red = True
  Green == Green = True
  _ == _ = False

public export
Show Metric where
  show Blue = "Blue"
  show Red = "Red"
  show Green = "Green"

||| The core fundamental data structure of the non-linear physics engine.
||| A 2-component coordinate representing a source and target (e.g. x and y).
public export
record Pixel (metric : Metric) (a : Type) where
  constructor MkPixel
  src : a
  tgt : a

||| Canonical unambiguous alias for chromogeometric 3-metric pixels.
public export
MetricPixel : Metric -> Type -> Type
MetricPixel = Pixel

public export
Eq a => Eq (Pixel metric a) where
  (MkPixel s1 t1) == (MkPixel s2 t2) = s1 == s2 && t1 == t2

public export
Show a => Show (Pixel metric a) where
  show (MkPixel s t) = "(" ++ show s ++ ", " ++ show t ++ ")"

||| Casts a Pixel from one metric index to another (phantom type cast).
public export
castMetric : {0 m2 : Metric} -> Pixel m1 a -> Pixel m2 a
castMetric (MkPixel s t) = MkPixel s t

||| Pixel multiplication in Wildberger's Box Arithmetic.
||| Iff b == c in [a,b] * [c,d] then the product is [a,d]
||| Otherwise, the product is Nothing.
public export
mulPixel : Eq a => Pixel metric a -> Pixel metric a -> Maybe (Pixel metric a)
mulPixel (MkPixel a b) (MkPixel c d) =
  if b == c then Just (MkPixel a d) else Nothing

