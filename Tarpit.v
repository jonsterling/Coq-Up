Require Import ZArith List.
Require Import Basics.

Set Implicit Arguments.
Open Scope nat_scope.

Module Tarpit. 
  Section DataTypes.
    Variable A : Type.

    CoInductive stream  : Type :=
    | SCons : A -> stream -> stream.

    CoFixpoint forever (x : A) : stream := SCons x (forever x).
    
    Record zipper := Zip
      { left  : stream ;
        focus : A ;
        right : stream
      }.

    Definition moveLeft (z : zipper) : zipper :=
      match z with
        | Zip (SCons l ls) c rs => Zip ls l (SCons c rs)
      end.
    
    Definition moveRight (z : zipper) : zipper :=
      match z with
        | Zip ls c (SCons r rs) => Zip (SCons c ls) r rs
      end.

    Definition setFocus (x : A) (z : zipper) :=
      match z with
        | Zip ls _ rs => Zip ls x rs
      end.

    Definition modFocus (f : A -> A) (z : zipper) :=
      match z with
        | Zip ls x rs => Zip ls (f x) rs
      end.

  End DataTypes.

  Definition tape := zipper nat.

  Section IO.
    CoInductive EffectTree {C : Type} {R : C -> Type} (A : Type) : Type :=
    | pure : A -> EffectTree A
    | eff  : forall (c : C), (R c -> EffectTree A) -> EffectTree A.

    Inductive IOC := Read | Write | Inc | Dec | L | R.
    Definition FIO := @EffectTree IOC (fun _ => unit).
  End IO.

  Section Haskell.
    CoInductive HS_IO : Type -> Type :=
    | HS_return : forall (A : Type), A -> HS_IO A
    | HS_bind : forall (A B : Type), HS_IO A -> (A -> HS_IO B) -> HS_IO B
    | HS_write : nat -> HS_IO unit
    | HS_read : HS_IO nat
    | HS_id : forall (A : Type), HS_IO A -> HS_IO A.
  End Haskell.


  Section Compiler.
    CoInductive colist A : Type :=
    | conil  : colist A
    | cocons : A -> colist A -> colist A.
    Implicit Arguments conil [A].
    
    Definition prog := colist IOC.
    CoFixpoint eval {A} (mx : FIO A) (t : tape) : HS_IO A :=
      let tapeMod := fun f cont => HS_id (eval (cont tt) (f t)) in
      match mx with
        | pure x => HS_return x
        | eff Write cont => HS_bind (HS_write (focus t)) (fun _ => eval (cont tt) t)
        | eff Read cont => HS_bind HS_read (fun x => eval (cont tt) (setFocus x t))
        | eff L cont => tapeMod (@moveLeft _) cont
        | eff R cont => tapeMod (@moveRight _) cont
        | eff Inc cont => tapeMod (modFocus (fun x => x + 1)) cont
        | eff Dec cont => tapeMod (modFocus (fun x => x - 1)) cont
      end.

    CoFixpoint compile (p : prog) : FIO _ :=
      match p with
        | conil => pure tt
        | cocons x xs => eff x (fun _ => compile xs)
      end.
  End Compiler.
End Tarpit.

Module Examples.
  Import Tarpit.

  Infix " ::: " := cocons (right associativity, at level 100).
  CoFixpoint testProgram : prog :=
    (Read ::: Dec ::: Write ::: Inc ::: Inc ::: Inc ::: Write ::: testProgram).
  
  Definition zeroes : stream nat := forever 0.
  Definition main := eval (compile testProgram) (Zip zeroes 1 zeroes).
End Examples.

Import Tarpit.
Extract Inductive HS_IO => "Prelude.IO" [ "Prelude.return" "(Prelude.>>=)" "Prelude.print" "((Prelude.fmap Prelude.read Prelude.getLine) :: Prelude.IO Prelude.Integer)" "Prelude.id" ].
Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n==0 then fO () else fS (n-1))".
Extract Inlined Constant plus => "(Prelude.+)".
Extract Inlined Constant minus => "(Prelude.-)".
Extract Inlined Constant mult => "(Prelude.*)".
Extract Inductive colist => "([])" [ "[]" "(:)" ].
Extract Inductive list => "([])" [ "[]" "(:)" ].
Extract Inductive unit => "()" [ "()" ].

Extraction Language Haskell.
Extraction "Example" Examples.