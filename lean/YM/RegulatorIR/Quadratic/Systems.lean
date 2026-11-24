import YM.RegulatorIR.Quadratic.Vapor

/-!
Invisible volume constants don't enter stiffness equations (one endpoint on
cover is kept independent). Uniform row bounds over positions at fixed
regulator translation cell carry no scale rate promise. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Quadratic
open Lattice Function Budget Motion Budget.Layer Budget.Packet Budget.Deck Step Diagram
open scoped ENNReal NNReal BigOperators Classical Topology Matrix
variable {W X I J: Type} {P:ℝ} {c:ℝ}
variable {A:Deck P W X}{B:Deck P I J}
def clipL {X Y:Type}(b:X→ Prop) (F:Layer X Y) : Layer X Y:=fun x y=>if b x then F x y else 0
lemma clip_f (b:X→ Prop)(A:Deck P W X)(B:Deck P I J)(F:Layer W I):fmat A B (clipL (b ∘ A.orbit) F)= clipL b (fmat A B F):=by
 ext1 i j
 unfold fmat clipL wrapL forwardCost Stalk.collect paint; simp_rw [Function.comp_apply,A.placed]; split_ifs <;> simp
-- issue expected type reduces ext? rfl

-- bulk inputs hypothesized only on quadratic cover, incl literal kernels Q_r and relative rooted gamma. F i=active interior nontrunks, other constraints killed. All real lattice. No orb Hessian assertion.
variable (A B)

def stableL (c:ℝ)(K:Layer W W)(Q:Layer I W): Layer W W:= K+c • lap (Function.swap Q) Q
structure Bedload (A:Deck P W X) (B:Deck P I J) (c:ℝ)(act: X→ Prop)(K:Layer W W)(K':Layer I I)(Q:Layer I W)(D:Layer W I)(N:Layer W W) :Prop where
 rows : Billed K ∧ Billed Q ∧ Billed (Function.swap Q) ∧ Billed D ∧ Billed N
 sym : Sym A A K ∧ Sym B A Q ∧ Sym A B D ∧ Sym A A N
 symmetric : Function.swap K=K
 mean (x:W) y : ¬act (A.orbit x) → D x y=0
 inverse (x:W) y : ¬act (A.orbit x) → N x y=0
 sheet : clipL (act ∘ A.orbit) (lap (stableL c K Q) D)=clipL (act ∘ A.orbit) (c • Function.swap Q)
 feather : clipL (act ∘ A.orbit) (lap (stableL c K Q) N)=clipL (act ∘ A.orbit) (ID W)
 energy : c • (ID I-lap Q D)=K'

-- cut some matrices
variable [Fintype X][Fintype J]

def diagStiff (c:ℝ) (K:Matrix X X ℝ)(Q: Matrix J X ℝ):= K+c • (Q.transpose*Q)
structure GridQ [DecidableEq X][DecidableEq J] (c:ℝ)(act:X→Prop)(K: Matrix X X ℝ)(K':Matrix J J ℝ)(Q:Matrix J X ℝ)(D:Matrix X J ℝ)(N:Matrix X X ℝ):Prop where
 turn : K.transpose=K
 means (x:X) y : ¬ act x→ D x y=0
 inverse x y : ¬act x→ N x y=0
 passes i j : act i → (diagStiff c K Q*D) i j=c*Q j i
 fees i j : act i →(diagStiff c K Q*N) i j = (1:Matrix X X ℝ) i j
 stiff : c • (1-Q*D)=K'
namespace Bedload
variable {A B} [DecidableEq X][DecidableEq J]{act:X→Prop}{K N:Layer W W}{K':Layer I I}{Q:Layer I W}{D:Layer W I} (S: Bedload A B c act K K' Q D N)
include S
omit [Fintype X][DecidableEq X][DecidableEq J] in
lemma stableF : fmat A A (stableL c K Q) = diagStiff c (fmat A A K) (fmat B A Q):=by
 obtain ⟨ha,hb,hc,h'⟩:=S.rows;rw [stableL,fmat_add A A ha ((hc.lap hb).smul _),fmat_scale,fmat_mul A B A hc hb S.sym.2.1,fmat_trans B A Q S.sym.2.1];rfl
lemma grid : GridQ c act (fmat A A K) (fmat B B K') (fmat B A Q) (fmat A B D) (fmat A A N):=by
 obtain ⟨ha,hb,hc,H,hx⟩:= S.rows; obtain ⟨hh,ht,hM,hF⟩:= S.sym
 have hR:Billed (stableL c K Q):=ha.add ((hc.lap hb).smul c)
 have hs (T: Type)(U : Type) (V:Deck P T U)(L:Layer W T)(hl:∀ x y,¬ act (A.orbit x) → L x y=0) i j (hh : ¬act i): fmat A V L i j=0:=by
    unfold fmat wrapL forwardCost Stalk.collect paint; simp_rw [hl _ _ (fun he=> hh ((A.placed i) ▸ he)),zero_mul,tsum_zero]
 refine ⟨fmat_sym A hh S.symmetric, hs I J B D S.mean, hs W X A N S.inverse,?_,?_,?_⟩
 · have he:= congr_arg (fmat A B) S.sheet;rw [clip_f,clip_f,fmat_scale,fmat_mul A A B hR H hM,S.stableF,fmat_trans B A Q ht] at he
   intro i j hi; have he:=congr_arg (fun x: Matrix X J ℝ=>x i j) he; simp only [clipL,if_pos hi] at he; exact he
 · have he:=congr_arg (fmat A A) S.feather;rw [clip_f,clip_f,fmat_mul A A A hR hx hF,S.stableF,fmat_id] at he
   intro i j hi; have he:=congr_arg (fun x: Matrix X X ℝ=> x i j) he;simpa only [clipL,if_pos hi] using he
 have he:= congr_arg (fmat B B) S.energy; rw [fmat_scale, fmat_sub B B billed_id (hb.lap H),fmat_id, fmat_mul B A B hb H hM] at he; exact he
end Bedload

-- finite block equations implemented later. joint blocks
variable {A B}
def glued {X Y:Type}(F:Layer X X)(H:Layer X Y)(T:Layer Y X)(L:Layer Y Y): Layer (X⊕Y) (X⊕Y):= fun a b=> Sum.elim (fun i=>Sum.elim (F i) (H i) b) (fun i=> Sum.elim (T i) (L i) b) a
def hoses (D:Layer W I): Layer (W⊕I) (W⊕I):= glued 0 D 0 (ID I)
def petals (K:Layer W W): Layer (W⊕I) (W⊕I):= glued K 0 0 0
-- deck transport projection
omit [Fintype X] [Fintype J]
variable (A B)

def from_fst (x:X) : Stalk A.orbit x≃ Stalk (Step.combine A B).orbit (.inl x):= by
 refine Equiv.ofBijective (fun i=>⟨.inl i.val,congr_arg Sum.inl i.property⟩) ⟨fun a b h=> ?_,?_⟩
 · exact Subtype.ext (Sum.inl.inj (Subtype.mk.inj h))
 rintro ⟨y|y,he⟩
 · exact ⟨⟨y,Sum.inl.inj he⟩,rfl⟩
 contradiction

def from_snd (x:J): Stalk B.orbit x≃ Stalk (Step.combine A B).orbit (.inr x):=by
 refine Equiv.ofBijective (fun i=>⟨.inr i.val,congr_arg Sum.inr i.property⟩) ⟨fun a b h=> ?_,?_⟩
 · exact Subtype.ext (Sum.inr.inj (Subtype.mk.inj h))
 rintro ⟨y|y,he⟩
 · contradiction
 exact ⟨⟨y,Sum.inr.inj he⟩,rfl⟩
lemma fmat_glue (F:Layer W W)(H:Layer W I)(T:Layer I W)(L:Layer I I):fmat (Step.combine A B) (Step.combine A B) (glued F H T L)=glued (fmat A A F) (fmat A B H) (fmat B A T) (fmat B B L):=by
 ext1 i j; cases i <;> cases j <;> rename_i a b <;> unfold fmat wrapL forwardCost Stalk.collect
 · rw [← (from_fst A B b).tsum_eq]; rfl
 · rw [← (from_snd A B b).tsum_eq];rfl
 · rw [← (from_fst A B b).tsum_eq];rfl
 rw [← (from_snd A B b).tsum_eq];rfl
lemma fmat_dark : fmat A B 0=0:=by ext i j; change wrapL A B 0 i j=0; simp [wrapL,forwardCost,Stalk.collect, paint]
lemma fmat_hose [DecidableEq J](D:Layer W I): fmat (Step.combine A B) (Step.combine A B) (hoses D) = glued 0 (fmat A B D) 0 (1:Matrix J J ℝ):= by rw [hoses, fmat_glue, fmat_id,fmat_dark,fmat_dark]; rfl
lemma fmat_petals (D:Layer W W): fmat (Step.combine A B) (Step.combine A B) (petals D) = petals (I:=J) (fmat A A D):= by rw [petals,fmat_glue,fmat_dark,fmat_dark,fmat_dark]; rfl
end YM.RegulatorIR.Quadratic
