module Example where

import qualified Prelude

data Unit =
   Tt

data Nat =
   O
 | S Nat

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p -> S (plus p m)}

data Stream a =
   SCons a (Stream a)

forever :: a1 -> Stream a1
forever x =
  SCons x (forever x)

data Zipper a =
   Zip (Stream a) a (Stream a)

zipper_rect :: ((Stream a1) -> a1 -> (Stream a1) -> a2) -> (Zipper a1) -> a2
zipper_rect f z =
  case z of {
   Zip x x0 x1 -> f x x0 x1}

zipper_rec :: ((Stream a1) -> a1 -> (Stream a1) -> a2) -> (Zipper a1) -> a2
zipper_rec =
  zipper_rect

left :: (Zipper a1) -> Stream a1
left z =
  case z of {
   Zip left0 focus0 right0 -> left0}

focus :: (Zipper a1) -> a1
focus z =
  case z of {
   Zip left0 focus0 right0 -> focus0}

right :: (Zipper a1) -> Stream a1
right z =
  case z of {
   Zip left0 focus0 right0 -> right0}

moveLeft :: (Zipper a1) -> Zipper a1
moveLeft z =
  case z of {
   Zip left0 c rs ->
    case left0 of {
     SCons l ls -> Zip ls l (SCons c rs)}}

moveRight :: (Zipper a1) -> Zipper a1
moveRight z =
  case z of {
   Zip ls c right0 ->
    case right0 of {
     SCons r rs -> Zip (SCons c ls) r rs}}

setFocus :: a1 -> (Zipper a1) -> Zipper a1
setFocus x z =
  case z of {
   Zip ls focus0 rs -> Zip ls x rs}

modFocus :: (a1 -> a1) -> (Zipper a1) -> Zipper a1
modFocus f z =
  case z of {
   Zip ls x rs -> Zip ls (f x) rs}

type Tape = Zipper Nat

data Free c r a =
   Pure a
 | Eff c (r -> Free c r a)

free_rect :: (a3 -> a4) -> (a1 -> (a2 -> Free a1 a2 a3) -> (a2 -> a4) -> a4)
             -> (Free a1 a2 a3) -> a4
free_rect f f0 f1 =
  case f1 of {
   Pure y -> f y;
   Eff c p -> f0 c p (\y -> free_rect f f0 (p y))}

free_rec :: (a3 -> a4) -> (a1 -> (a2 -> Free a1 a2 a3) -> (a2 -> a4) -> a4)
            -> (Free a1 a2 a3) -> a4
free_rec =
  free_rect

data IOC =
   Write
 | Plus Nat
 | Read
 | L
 | R

iOC_rect :: a1 -> (Nat -> a1) -> a1 -> a1 -> a1 -> IOC -> a1
iOC_rect f f0 f1 f2 f3 i =
  case i of {
   Write -> f;
   Plus x -> f0 x;
   Read -> f1;
   L -> f2;
   R -> f3}

iOC_rec :: a1 -> (Nat -> a1) -> a1 -> a1 -> a1 -> IOC -> a1
iOC_rec =
  iOC_rect

type FIO a = Free IOC Unit a

zeroes :: Stream Nat
zeroes =
  forever O

type HS_IO a = IO a

hS_return :: a1 -> HS_IO a1
hS_return = return

type Prog = ([]) IOC

eval :: (FIO a1) -> Tape -> HS_IO a1
eval mx t =
  let {tapeMod = \f cont -> eval (cont Tt) (f t)} in
  case mx of {
   Pure x -> hS_return x;
   Eff c cont ->
    case c of {
     Write -> (>>=) (print (focus t)) (\x -> eval (cont Tt) t);
     Plus n -> tapeMod (modFocus (\x -> plus n x)) cont;
     Read ->
      (>>=) ((fmap read getLine) :: IO Z) (\x ->
        eval (cont Tt) (setFocus x t));
     L -> tapeMod moveLeft cont;
     R -> tapeMod moveRight cont}}

compile :: Prog -> FIO Unit
compile p =
  case p of {
   [] -> Pure Tt;
   (:) x xs -> Eff x (\x0 -> compile xs)}

testProgram :: Prog
testProgram =
  (:) Read ((:) Write ((:) (Plus (S (S (S (S O))))) ((:) Write [])))

compiledTest :: HS_IO Unit
compiledTest =
  eval (compile testProgram) (Zip zeroes (S O) zeroes)

