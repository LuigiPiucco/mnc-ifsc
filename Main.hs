{-# LANGUAGE RankNTypes #-}
module Main where

import Codec.Picture (PixelRGBA8 (..), writePng)
import Control.Monad
import Data.Array.Accelerate
  ( Acc,
    All (..),
    Any (..),
    Array,
    DIM2,
    Elt,
    Exp,
    Generic,
    Lift (..),
    Matrix,
    Plain,
    Unlift,
    Vector,
    Z (..),
    (:.) (..),
  )
import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate.Data.Complex
import Data.Array.Accelerate.LLVM.PTX
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.Sugar.Elt
import qualified Data.Complex as C
-- import Graphics.Amusing
import Graphics.Rasterific hiding (Vector)
import Graphics.Rasterific.Texture
import Prelude.Unicode
import Text.Printf

type Pendulum a b = (a, b)

zs :: Pendulum a b -> a
zs (zs,  _) = zs

ps :: Pendulum a b -> b
ps (_, ps) = ps

type Pair a = (a, a)

g :: (RealFrac a, A.RealFloat a, Elt a) => Exp a
g = 9.81

origin ::
  (RealFrac a, A.RealFloat a, Elt a) =>
  Exp (Pair (Complex a))
origin = A.constant (0 :+ 0, 0 :+ 0)

zero ::
  (RealFrac a, A.RealFloat a, Elt a) =>
  Exp (Pair a)
zero = A.constant (0, 0)

one ::
  (RealFrac a, A.RealFloat a, Elt a) =>
  Exp (Pair (Complex a))
one = A.constant (1 :+ 0, 1 :+ 0)

calc ::
  forall a.
  (RealFrac a, A.RealFloat a, Elt a) =>
  Exp a ->
  Exp a ->
  Exp a ->
  Exp (Pendulum (Pair (Complex a)) (Pair a)) ->
  Exp (Pendulum (Pair (Complex a)) (Pair a))
calc m1 m2 dt pendulum =
  let (zs, ps) = A.unlift pendulum
      zs :: Exp (Pair (Complex a))
      ps :: Exp (Pair a)
      (z1 :: Exp (Complex a), z3 :: Exp (Complex a)) = A.unlift zs
      (p1 :: Exp a, p3 :: Exp a) = A.unlift ps
      i1 = inertia z1 m1
      i3 = inertia z3 m2
      angleDiff = phase z1 - phase z3
      commonFactor = (magnitude z3 / i1)/(18 * i3 * cos angleDiff**2 -
                        8 * absSquared z3 * (3 * m2 + m1))
      ω1 = commonFactor * m1 *
             (3 * magnitude z1 * p3 * cos angleDiff - 2 * magnitude z3 * p1)
      ω3 = commonFactor/i3 *
             (3 * m1 * magnitude z1 * i3 * p1 * cos angleDiff - 2 * i1 * magnitude z3 * p3 * (3 * m2 + m1))
      v1 = cis(ω1 * dt)
      v3 = cis(ω3 * dt)
      pCommonFactor = 6 * magnitude (z1 / z3) * i3 * ω1 * ω3 * sin angleDiff
      p1' = (-pCommonFactor) - g * (m1/2 + m2) * magnitude z1 * cos(phase z1)
      p3' = pCommonFactor - g * m2 * magnitude z3 / 2 * cos(phase z3)
   in A.lift
        ( (z1 * v1, z3 * v3),
          (p1 + p1' * dt, p3 + p3' * dt)
        )
  where
    absSquared z = real (z * conjugate z)
    inertia z m = m * absSquared z / 12

inited ::
  (RealFrac a, A.RealFloat a, Elt a) =>
  Int ->
  Exp (Pair (Complex a)) ->
  Acc (Vector (Pendulum (Pair (Complex a)) (Pair a)))
inited frames zs = A.fill (A.constant $ Z :. 1) $ A.lift (zs, zero)

compute ::
  (RealFrac a, A.RealFloat a, Elt a) =>
  ( Exp (Pendulum (Pair (Complex a)) (Pair a)) ->
    Exp (Pendulum (Pair (Complex a)) (Pair a))
  ) ->
  Acc (Vector (Pendulum (Pair (Complex a)) (Pair a))) ->
  Acc (Vector (Pendulum (Pair (Complex a)) (Pair a)))
compute calc mat =
  let n = indexHead $ A.shape mat
      last = A.replicate (A.constant $ Z :. 1 :: Exp (Z :. Int)) $ A.slice mat (A.lift $ Z :. n - 1)
      new = A.map calc last
   in mat A.++ new

computation ::
  forall a.
  (RealFrac a, A.RealFloat a, Elt a) =>
  Int ->
  Acc (Vector (Pendulum (Pair (Complex a)) (Pair a))) ->
  ( Acc (Vector (Pendulum (Pair (Complex a)) (Pair a))) ->
    Acc (Vector (Pendulum (Pair (Complex a)) (Pair a)))
  ) ->
  Exp (Pair (Complex a)) ->
  Acc (Vector (Pair (Complex a)))
computation frames inited compute zs =
  A.map mapper ran
  where
    pred mat =
      let (A.unlift -> Z :. i :: Z :. Exp Int) = A.shape mat
          in A.unit $ i A.< A.constant frames

    mapper :: Exp (Pendulum (Pair (Complex a)) (Pair a)) -> Exp (Pair (Complex a))
    mapper (A.unlift -> pendulum :: Pendulum (Exp (Pair (Complex a))) (Exp (Pair a))) =
      let (z, _) = pendulum
       in z

    ran :: Acc (Vector (Pendulum (Pair (Complex a)) (Pair a)))
    ran = A.awhile pred compute inited

simulatePendulums ::
  (RealFrac a, A.RealFloat a, Elt a) =>
  (C.Complex a, a) ->
  (C.Complex a, a) ->
  a ->
  a ->
  [Pair (C.Complex a)]
simulatePendulums (z1, m1) (z2, m2) t dt = A.toList $ run computation'
  where
    frames = ceiling $ t / dt
    zs = A.constant (z1, z2)
    calc' = calc (A.constant m1) (A.constant m2) (A.constant dt)
    inited' = inited frames zs
    compute' = compute calc'
    computation' = computation frames inited' compute' zs

skip :: Int
skip = 2

paint :: Double -> (Int, Pair (Complex Double)) -> IO ()
paint m (i, (z1@(x1 C.:+ y1), z2@(x2 C.:+ y2))) =
  when (mod i skip == 0) $ do
    putStrLn $ "z1 = " ++ show z1
    putStrLn $ "z2 = " ++ show z2
    let side = 2000 :: Int
        width = 15
        x1' = realToFrac $ (fromIntegral side / 2) * (1 + x1 / m)
        y1' = realToFrac $ (fromIntegral side / 2) * (1 - y1 / m)
        x2' = realToFrac $ (fromIntegral side / 2) * (1 + (x2 + x1) / m)
        y2' = realToFrac $ (fromIntegral side / 2) * (1 - (y2 + y1) / m)
        bg = PixelRGBA8 0x0c 0x0a 0x20 255
        lineColor = PixelRGBA8 0xdf 0x85 0xff 255
        img = renderDrawing side side bg $
          withTexture (uniformTexture lineColor) $ do
            stroke width JoinRound (CapRound, CapRound) $
              line
                (V2 (fromIntegral side / 2) (fromIntegral side / 2))
                (V2 x1' y1')
                ++ line (V2 x1' y1') (V2 x2' y2')
    writePng (printf "results/double-pendulum-%05v.png" $ div i skip) img

main :: IO ()
main = do
  let z1 = C.cis (pi/4) :: Complex Double
      z2 = C.cis (pi/4) :: Complex Double
      list = zip [0 ..] $ simulatePendulums
                            (z1, 1) (z2, 1)
                            (50 * fromIntegral skip) (1 / (60 * fromIntegral skip))
  forM_ list $ paint $ C.magnitude z1 + C.magnitude z2
