import YM.OPE.Levy.Theory
import YM.OPE.Levy.Inverse

/-!
# Inserting engineering-graded moving input panels into the actual upstream OPE

Use finite Ward/column filtration splitting, not a presumed scalar
multiplicative factor shared by all labels. Keep one Reader also in
testing. Only claims strict power margins here; comparing at *two*
moving scales with bounded ratio would require more for coefficients.
-/
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.OPE.Levy
open Filter Set Function Table Ward Orbits Extraction Climb Next.UVStress Spec
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (X:Scaling S) (H:Anchored U.sector.derivatives (path X) (isoPanel X))
local notation "Q" =>U.sector.derivatives
local notation "T" =>zstamp (path X)
local notation "A" => X.U
local notation "V" =>(Bel C.book)

def grade (d m:ℕ)(i:ℕ)(x:(Bel C.book).Field d):S.Field m := (R.cutTest m d) (A i d x)

include H
lemma upper_row (m d:ℕ)(hm:m≤d)(x:(Bel C.book).Field d):RateLE atTop T (fun i=>grade U R X d m i x) (-(m:ℝ)):=by
     let f:=R.cutTest m d
     have he : f.comp (planeAt (U:=Q) m hm).subtype=0:=by
       cases m with
       | zero => ext v; change R.cutTest 0 d v.val = 0; rw [show v.val=0 from (Submodule.mem_bot ℂ).mp v.2,map_zero]
       | succ m => ext v; obtain ⟨u,hu⟩:=v.2; change (R.cutTest _ _ v.val)=0; rw [←hu,R.cut_rise]; exact R.kills_lower _ _ (Nat.lt_add_one _) _
     let B:=Module.finBasis ℂ (S.Field m)
     let c(i: Fin (Module.finrank ℂ (S.Field m))):= ((B.coord i).comp f)
     have h₂ (i) (p:↥(planeAt (U:=Q) m hm)):c i p.val=0:= by change B.coord i ((f.comp (planeAt _ _).subtype) p) =_; rw [he]; apply map_zero
     have ha(i):= (B.sum_repr (grade U R X d m i x)).symm
     exact RateLE.congr (RateLE.sum (S:=Finset.univ) (f:=fun j i=>(c j (A i d x)) • B j) (zlarge (path X)) (fun b _=>by simpa only [add_zero,isoPanel,LinearEquiv.coe_coe] using (H d m hm x (c b) (fun v hv=> h₂ b ⟨v,hv⟩)).smul (RateLE.const (B b) (zlarge (path X))))) (Eventually.of_forall fun n=>(ha n).symm)

variable {I:Type}[Fintype I] (d:I→ℕ) (v:(i:I)→(Bel C.book).Field (d i))
def primary (X:Scaling S) (d:I→ℕ)(v:(i:I)→(Bel C.book).Field (d i)) (k:ℕ):Labels S d:= fun i=> X.U k (d i) (v i)
include U R H
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E](b:ℝ)
-- rise exactly into a common filtration presentation
lemma evaluated (M:ℕ→∀ e:I→ℕ,MultilinearMap ℂ (fun i=>S.Field (e i)) E)
       (hr:∀ (e:I→ℕ)(he:e≤d),∀ᶠ k in atTop,∀ v:(i:I)→S.Field (e i), M k e v=M k d (fun i=>(Q).rise (he i) (v i)))
       (hf:∀ (e:I→ℕ)(he:e≤d)(v:(i:I)→S.Field (e i)),RateLE atTop T (fun k=>M k e v) (weight e + b)):
       RateLE atTop T (fun k=> (M k d (primary X d v k))) b:=by
     let J:=fun i=>Fin (d i+1)
     let cost(j:(i:I)→J i):I→ℕ:=fun i=>(j i).val
     let φ(k:ℕ)(i:I)(j:J i):S.Field (d i) := (Q).rise (Nat.le_of_lt_succ j.isLt) (grade U R X (d i) j k (v i))
     let f (i:I)(j:J i) := (-(j.val:ℝ))
     have ht(k):primary X d v k=fun i=>(∑ j:J i,φ k i j):=by
       funext i
       change _=(∑ j:J i,(Q).rise _ _)
       rw [← (Q).arrival R.continuum.laws.toSymmetric R.lifts (primary X d v k i)]
       exact (R.reconstruct (d i) (d i) (le_refl _) (primary X d v k i)).symm
     let f' (k:ℕ)(j:(i:I)→J i)(i:I): S.Field (cost j i):=grade U R X _ (j i) k (v i)
     have hEq:∀ᶠ k in atTop, ∀ j: (i:I)→ J i, M k d (fun i=>φ k i (j i)) = M k (cost j) (f' k j) :=by
        exact eventually_all.mpr fun j=>((hr _ (fun i=>Nat.le_of_lt_succ (j i).isLt))).mono (fun k he=>(he (f' k j)).symm)
     apply RateLE.congr (RateLE.sum (f:=fun j k=>M k (cost j) (f' k j)) (S:=Finset.univ) (zlarge (path X)) (fun j _=> ?_)) (hEq.mono fun k hk=> by rw [ht k,MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun _ _=>(hk _).symm )
     let e:=cost j
     have he(q):=hf e (fun i=>Nat.le_of_lt_succ (j i).isLt) q
     have hw(i):RateLE atTop T (fun k=> f' k j i) (f i (j i)):=upper_row U R X H _ _ (Nat.le_of_lt_succ (j i).isLt) _
     have ht' := Orbits.contract (zlarge (path X)) (fun k=> M k e) he (fun k=>f' k j) (fun i=>f i (j i)) hw
     unfold weight f at ht'; rw [Finset.sum_neg_distrib] at ht';
     dsimp only [cost,e] at ht'; rw [add_comm,neg_add_cancel_left] at ht'; exact ht'

end YM.OPE.Levy
