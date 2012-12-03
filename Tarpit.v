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

    CoInductive colist : Type :=
    | conil  : colist
    | cocons : A -> colist -> colist.

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

  Section Haskell.
    CoInductive HS_IO : Type -> Type :=
    | HS_return : forall (A : Type), A -> HS_IO A
    | HS_bind : forall (A B : Type), HS_IO A -> (A -> HS_IO B) -> HS_IO B
    | HS_write : nat -> HS_IO unit
    | HS_read : HS_IO nat
    | HS_id : forall (A : Type), HS_IO A -> HS_IO A.
  End Haskell.

  Section Program.
    CoInductive EffectTree {C : Type} {R : C -> Type} (A : Type) : Type :=
    | pure : A -> EffectTree A
    | eff  : forall (c : C), (R c -> EffectTree A) -> EffectTree A.

    Inductive instruction := Read | Write | Inc | Dec | L | R.
    Definition io := @EffectTree instruction (fun _ => unit).
    Definition tape := zipper nat.
    Definition prog := colist instruction.

    CoFixpoint eval {A} (mx : io A) (t : tape) : HS_IO A :=
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

    CoFixpoint compile (p : prog) : io _ :=
      match p with
        | conil => pure tt
        | cocons x xs => eff x (fun _ => compile xs)
      end.
  End Program.

End Tarpit.

Module Notations.
  Import Tarpit.

  Infix " ::: " := cocons (right associativity, at level 100).

  (* A terminating program is a list of semicolon-separated
     instructions in [| ... |]. *)

  Notation "[| x ; .. ; y |]" := (x ::: .. (y ::: (conil _)) ..).

  (* [| a ; b ; c |> r concatenates the program in the brackets with
     the program [r]; this can be used for making coinductive
     programs, such as REPLs. *)

  Notation "[| x ; .. ; y |> r" := (x ::: .. (y ::: r) ..)
                                    (at level 100).
End Notations.

Module Examples.
  Import Tarpit.
  Import Notations.

  CoFixpoint testProgram : prog :=
    [| Read ; Dec ; Write ; Inc ; Inc ; Inc ; Write |> testProgram.
     
  Definition zeroes : stream nat := forever 0.
  Definition main := eval (compile testProgram) (Zip zeroes 1 zeroes).
End Examples.


Module Extractions.
  Import Tarpit.
  Extraction Language Haskell.
  Extract Inductive HS_IO => "Prelude.IO" [ "Prelude.return" "(Prelude.>>=)" "Prelude.print" "((Prelude.fmap Prelude.read Prelude.getLine) :: Prelude.IO Prelude.Integer)" "Prelude.id" ].
  Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
    "(\fO fS n -> if n==0 then fO () else fS (n-1))".
  Extract Inlined Constant plus => "(Prelude.+)".
  Extract Inlined Constant minus => "(Prelude.-)".
  Extract Inlined Constant mult => "(Prelude.*)".
  Extract Inductive colist => "([])" [ "[]" "(:)" ].
  Extract Inductive list => "([])" [ "[]" "(:)" ].
  Extract Inductive unit => "()" [ "()" ].
End Extractions.

Extraction "Example" Examples.