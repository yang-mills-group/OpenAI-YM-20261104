import YM.RG17.GateFlow
import YM.RG17.Gauges
/-!
# Horizon zero rolling rights on single mixed lane

Support fixed, derivative and exterior costs explicit. Keep location of
weights in true coupling coordinate convention. Charge absolute stencil
with all masks. Optional single-height lettering (when bought with
`Pegs`) and costs H returned, so producer can price those if desired
(not Lambda; may need extra order). Spatial demands still on regulator
not assumed on Final. Using single exterior shape sufficient here
and complete vacuum denominator in Gathers/Wound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits SharpGram Trace MeasureTheory RG12
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{F:Final C f S}
   {L:Layout F} (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
   (H : Services C f S) (loc : Located L) (Z:Ledger L) (T:Test 1)
set_option quotPrecheck false
abbrev cashier (_:Final C f S)(T:Test 1) : External C S:= ⟨0,Fin.elim0,T⟩
local notation "X"=>cashier F T
def amount (T:Test 1):=∫ x:Points 1,T x
open Nesting
private lemma oneCash {I : Type}[Fintype I](k:I→S.Tag)(x:I→E4)(h:Injective x) (z:Points 1) :
    whole S x (voices k) ((X).offset z) (X).labels = Orbits.moment S x (voices k):=by
   let y:= (X).offset z
   have hx : Injective (beside x y):=beside_distinct.mpr ⟨h,injective_of_subsingleton _,fun _ j=> j.elim0⟩
   let w:=Orbits.tags (stages (voices k) (X).labels)
   have he:= Sparse.Undo.restrict (Sparse.momentIdentity (S:=S) (spectator F none) F.room.kernel (spectate_respects F none)) _ hx Sum.inl Sum.inl_injective w (fun i hi => ?_)
   swap
   · cases i with
     | inr i=> exact i.elim0
     | inl j=> exact (hi j rfl).elim
   exact he
lemma bills {n:ℕ}{d:Fin n→ℕ}(v:Labels S d) (ψ:Test n) {r:ℝ}(hr:0<r):
    appeared F v X r ψ= amount T * plate v r ψ:=by
   rw [physicalPlate F v ψ hr,amount, ← MeasureTheory.integral_mul_const]; apply integral_congr_ae; filter_upwards with z
   refine congr_arg _ (ψ.apply_eq fun x hx=> ?_); exact oneCash T (tags v) (posed r x) (posed_on hx hr) _
lemma costOut (y:S.Field 0): (X).charge F 0 y= amount T * blank F none y:=by
   rw [amount, ← MeasureTheory.integral_mul_const]; apply integral_congr_ae; filter_upwards with z
   refine congr_arg _ ?_
   let u : Unit → S.Tag:=fun _=>⟨0,y⟩
   exact (oneCash T u (sole _) (injective_of_subsingleton _) z).trans
       (Short.tagged F u _ none (injective_of_subsingleton _)).symm
variable {n:ℕ}{d:Fin n→ℕ} (v:(i:Fin n)→Slot C (d i)) {R:ℕ}
include H
-- Optional single-height • all inputs representing a physically exact oriented mix via tents.
def Paid (L:Layout F)(r:ℝ)(x:(i:Fin n)→ C.label (d i)) :=fun i=> mass C _ (L.shift (d i) r (x i))
lemma individual {u}{B:Lenses.Mantle F u}(hp:Pegs B L)(w:(i:Fin n)→Free C (d i)): ∃ x:ℝ→ (i:Fin n)→ C.label (d i),∀ᶠ r in home,
    (∀ i, Paid L r (x r) i ≤ 2*C.path.levels.clock.hatBeta (L.level r)^Lenses.price (d i)* ‖w i‖) ∧
      ∀ i, master L (d i) r (x r i)= L.frame (d i) r (w i):=by
   have he: ∀ᶠ r in home, ∀ i:Fin n, ∃ x:C.label (d i), mass C _ (L.shift (d i) r x) ≤ 2*C.path.levels.clock.hatBeta (L.level r)^Lenses.price (d i)* ‖w i‖∧
       master L _ r x=L.frame (d i) r (w i):=by
     filter_upwards [eventually_all.mpr (fun i=> engineeringPass B L H hp (d i))] with r hr i
     let D:= d i
     obtain ⟨x,hx,Hx⟩:= (hr i).1 (w i)
     obtain ⟨y,rfl⟩:= (L.shift D r).surjective x; exact ⟨y,hx,Hx⟩
   rw [eventually_iff_exists_mem] at he; obtain ⟨K,hK,he⟩:=he
   choose! x hx hv using fun r i (h:r∈K)=>he r h i
   exact ⟨x, mem_of_superset hK (fun r hr=> ⟨fun i=>hx r i hr,fun i=>hv r i hr⟩)⟩
include P
omit H
lemma perches (x:ℝ→(i:Fin n)→C.label (d i)) (hp:∀ᶠ r in home,∀ i,master L (d i) r (x r i)= stems L v r i) :
    ∃ p:Seats C d, (∀ i r,p i (Fin.last (d i)) r=x r i) ∧ (∀ i j, j ≠ Fin.last (d i) → ∀ r,p i j r=0) ∧ Weights L v p:=by
   let p i (j:Fin (d i + 1))(r:ℝ) : C.label j := if h:j=Fin.last (d i) then h.symm ▸ (show C.label (Fin.last (d i)) from x r i) else 0
   have hpos i r : p i (Fin.last (d i)) r=x r i:=by unfold p; rw [dif_pos rfl]
   have hneg(i) (j:Fin (d i+1)) (he:j≠Fin.last (d i)) (r):p i j r=0:=dif_neg he
   refine ⟨p,hpos,hneg,hp.mono (fun r hr i=>?_ )⟩
   rw [Finset.sum_eq_single_of_mem (a:=Fin.last (d i)) (Finset.mem_univ _)]
   · change stems _ _ r i= F.sector.derivatives.rise (Fin.last (d i)|>.is_le) (master L _ r _)
     rw [hpos]; change stems L v r i= F.sector.derivatives.rise (le_refl (d i)) (master L (d i) r (x r i)); rw [hr i]; exact (F.sector.derivatives.arrival P.continuum.laws.toSymmetric P.lifts _).symm
   intro j _ hj; simp [chair,hneg i j hj]

omit P
variable (A:Ports C) (l:Filter ℝ) (p:Seats C d) (ψ:Test n)

structure Lane (Z: Ledger L) (A: Ports C) (T:Test 1) (v:(i:Fin n)→Slot C (d i)) (p:Seats C d)(l:Filter ℝ)(ψ:Test n) (R:ℕ)(e:ℝ) : Prop where
    estimates : ∃ (c a:ℝ)(j k:ℕ),0≤c∧0<a∧ ∀ᶠ r in l, ∃ M: UVIndex→C.label 0,
       ∀ b:ℝ, Demand j ψ b→ ∀ᶠ i in L.lens, (‖bank L p r ψ (cashier F T) i-headMark L (cashier F T) 0 r i (M i)‖ ≤ c*r^a*b)∧
         ‖M i-standing L (fun j r=> A.marked v 0 j r ψ) R r i‖ ≤ c* ledgerCoupling L r i^e* Z.Λ r ^ k*b -- e chosen exponent

include P H loc
lemma dispensed (hl:l ≤ home) (h:Weights L v p){e:ℝ} (hz:Lane Z A T v p l ψ R e):
   ∃ (c a:ℝ)(j k:ℕ),0≤c ∧ 0<a ∧ ∀ᶠ r in l, ∃ x:C.label 0, ∀ b:ℝ,Demand j ψ b →
     (‖amount T‖ * ‖plate (stems L v r) r ψ-send0 C x‖ ≤ c*r^a*b) ∧
       ‖x - forecast Z R (A.marked v 0) r ψ‖≤ c* Z.g r^e* Z.Λ r^k * b :=by
   obtain ⟨c,a,j,k,hc,ha,hJ⟩:=hz.estimates
   letI : L.lens.NeBot := L.notbot
   refine ⟨c,a,j,k,hc,ha,?_⟩
   filter_upwards [hJ,positiveLength.filter_mono hl,(blank_master Z loc).filter_mono hl,(limitBank P H L loc X p h ψ.hasCompactSupport ψ.tsupport_subset).filter_mono hl,(loc.level.growing.eventually_ge_atTop (C.ref 0)).filter_mono hl] with r hr hi hZ hp hR
   obtain ⟨M,hM⟩:=hr; obtain ⟨b,hb⟩:=demandAccessible j ψ
   let f i := ledgerCoupling L r i
   have hf:Tendsto f L.lens (𝓝 (Z.g r)) := (Z.fuse_at r).mono_left L.certified
   have he : Tendsto (fun i=> c*f i^e * Z.Λ r^k) L.lens (𝓝 (c*Z.g r^e* Z.Λ r^k)):= ((hf.rpow_const (.inl (Z.positive r).ne')).const_mul _).mul_const _
   let y(i:UVIndex):= standing L (fun j r=> A.marked v 0 j r ψ) R r i
   let z:= forecast Z R (A.marked v 0) r ψ; have hz:Tendsto y L.lens (𝓝 z):= standingLimit Z ..
   have hy:∀ᶠ i in L.lens, ‖M i‖ ≤ ‖z‖ + (c*Z.g r^e* Z.Λ r^k)*b + 1:=by
       filter_upwards [hM b hb, (hz.norm.add (he.mul_const b)).eventually (ge_mem_nhds (lt_add_one _))] with i hi hx
       refine le_trans (norm_le_norm_add_norm_sub (y i) (M i)) ?_; rw [norm_sub_rev]; exact (add_le_add_right hi.2 ‖y i‖).trans hx
   obtain ⟨g,hg,hg',m,hm⟩:=Next.UVStress.finite_extract M _ hy
   refine ⟨m,fun b hb=>?_⟩
   refine ⟨?_, le_of_tendsto_of_tendsto ((hm.sub (hz.mono_left hg)).norm) ((he.mono_left hg).mul_const b) (((hM b hb).filter_mono hg).mono fun _ hi=> hi.2)⟩
   have he:= ((hp ψ subset_rfl).mono_left hg|>.sub (limitHead L X hg hm hR)).norm
   rw [← norm_mul,mul_sub, ← hZ m, ← bills (F:=F), ← costOut (F:=F)]; rotate_left
   · exact hi
   exact le_of_tendsto he (((hM b hb).filter_mono hg).mono fun _ hi=> hi.1)
end YM.RG17
