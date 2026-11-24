import YM.SignedWilsonExpansion.Dancer.Stitch
/-!
# Application through filed garment vote wrapped on actual path
- Uses V coordinates, β monitors synchronized globally both homes.
- Activation clocks solved in calendar.Market.Reserving Helm
-/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.SignedWilsonExpansion.Dancer
open XSpace XSpace.Structure1 Normalize Future Gauge Filter Function Matrix
open WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ Stair
open Purchases Asymptotics Shell Lights Fort Coats Commission Maxwell Maxwell.Free Maxwell.Wick
open Precision Wilson Source WardBin Labels FVA2 FVA2.Dframe Homes PhysicalNext.Repeat.Quince.PreCost
open Extraction Order Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS BeamT
open MergeProof.East Next.Rank Ward Next.Rank.East PhysicalNext.Repeat.Legato Lattice FullVolume Cells
open Extra.Histories Pert UVClock PurchVoice
open scoped BigOperators Topology Classical
variable {G:Gauge} {C:Family G} {b d h t w n k u e:ℕ}{ι:Type}{L:Filter ι}{B r U ρ:ι→ℝ}
namespace Motif
open Stitch
variable {x:ℝ} {W':Initialize G} {V:∀h,Rays G h W'.hol}{K:Council C.labels} {E:Credit}{R:Realm G (e+1) E}
-- `x` as **global** r, `r` as local ρ for statement. `Λ_i` constructor may vary in ι separate monitors.
variable (H: (Bel C.book).Hierarchy) (f:Extraction.Order)(Y:ι→BeamT C) (N p j l:ι→ℕ)(A:ι→ (t:ℕ)→ C.label t≃ₗ[ℂ] C.label t)
structure Tune (z:ι→ PorchK W' C.labels V K R h k u) (H: (Bel C.book).Hierarchy)(f:Extraction.Order)(d:ℕ) (Y:ι→BeamT C)(N p j l:ι→ℕ)(A:ι→ (t:ℕ)→ C.label t≃ₗ[ℂ] C.label t)
    (L:Filter ι) (r ρ B U:ι→ℝ): Prop where
    enrolls (t:ℕ) (u:0<t)(p': t≤d): ∃ U', ∃ Ξ:ι→ℝ, ArmVote L B C t N p j l U' Ξ (fun i=> A i t)
    proper : ∀ᶠ i in L,(Y i).Given f H (ρ i)
    count : ∀ᶠ i in L,d ≤ (Y i).k
    dates : ∀ᶠ i in L,(Y i).V.k=j i
    pupil (t:ℕ) (u:0<t)(p':t≤d): ∀ᶠ i in L,Spinning C t ( j i ) (N i) (p i)
    spends : Spread B=O[L] U
    aligned : ∀ᶠ i in L,(z i).markW=C.S.a (j i+l i)/ r i
    weightJ : ∀ᶠ i in L,C.S.a (j i) ≤ ρ i
    late : ∀ᶠ i in L,j i < N i
    warm : pivotT L r ρ
    rise : ∀ᶠ i in L,0<r i
variable (z:ι→ PorchK W' C.labels V K R h k u)(h':C.Makes) (Q:Tune z H f d Y N p j l A L r ρ B U)
-- demanded multipliers
abbrev stake (r ρ : ι→ℝ)(d:ℕ)(i:ι):ℂ:= (ρ i / r i : ℝ)^d -- cast outside? lean reduces overloaded ℂ; check
abbrev standardV (r ρ:ι→ ℝ)(x: Sec G t)(i:ι):= worn ( Y i ) x (N i) (p i) (r i / ρ i)
abbrev saveV (ρ:ι→ℝ)(t:ℕ)(i:ι) := saveS C t (j i) (l i) (N i) (p i) (ρ i)
abbrev τF (r:ι→ℝ)(t:ℕ)(i:ι) := Purchases.furnace C t (j i) (l i) (N i) (p i) (r i) (A i t)
def standardMap (F : Labels.Frames G)(C:Family G)(Y:BeamT C)(N p:ℕ)(t:ℕ)(r:ℝ): Sec G t→ₗ[ℂ] C.label t:= Y.microphone (N,p) t ∘ₗ Pert.Scale.gear C.labels t r ∘ₗ (Free.fields C.labels t).symm.toLinearMap
-- map chosen early; junk outside needed caps.
abbrev curved (r ρ:ι→ℝ)(i:ι) (t:ℕ): Sec G t→ C.label t:= fun x=> stake r ρ t i • τF N p j l A ρ t i ( standardV Y N p r ρ x i )
noncomputable def Costume (r ρ:ι→ℝ)(i:ι): CutNet C.labels:=fun t=> if h:IsLinearMap ℂ (curved Y N p j l A r ρ i t) then h.mk' (curved Y N p j l A r ρ i t) else 0
include Q h'
-- shorten boilerplate `Stitch`. Need avoid overlapping namespace.work.H!
local notation "AZ"=> Costume Y N p j l A r ρ
local notation "¢"=> curved Y N p j l A r ρ
lemma study (i:Toon G t)(v:0<t)(w:t≤d): ∀ᶠ x in L, Attention C t (j x) (N x) (p x) i.size i.grade (ρ x) ( streak (Y x) (Logo G t i) (N x) (p x)) (Stitch.rep C (Logo G t i)):=by
     filter_upwards [Q.proper,Q.count,Q.dates,Q.late] with i hi ht he hs; rw [← he]; exact pulse_task _ hi (w.trans ht) (he.trans_lt hs) h' _
lemma opens (v:0<t)(w:t≤d): ∀ᶠ i in L, ∃ (T:C.label t→ₗ[ℂ] C.label t), savePage C t (j i) (N i) (p i)=T := by
    obtain ⟨X,F,h0⟩:= Q.enrolls _ v w; filter_upwards [ h0.fwd ] with i hi; exact ⟨ IsLinearMap.mk' _ (save_linear h' hi.1.late ((Nat.le_add_right ..).trans hi.1.age)), rfl ⟩ -- map constructor args
lemma saveOp (v:0<t)(w:t≤d): ∀ᶠ i in L, ∃ (T:C.label t→ₗ[ℂ] C.label t), saveV (C:=C) N p j l ρ t i=T := by
    filter_upwards [opens H f Y N p j l A z h' Q v w] with i ⟨V,hV⟩; exact ⟨ ((ρ i:ℂ)^t)⁻¹ • V,funext (fun y=> congr_arg (_ • ·) (congr_fun hV y)) ⟩
lemma tendon (v:0<t)(w:t≤d): ∀ᶠ i in L, ∃ T:C.label t→ₗ[ℂ] C.label t, τF N p j l A ρ t i=T :=by
    filter_upwards [saveOp H f Y N p j l A z h' Q v w] with i ⟨K,hK⟩; refine ⟨(C.labels.level t).scaled (Price.shrink C (j i+l i) (N i) (p i)) ∘ₗ ((A i t).symm.toLinearMap ∘ₗ K), funext (fun y=>?_ )⟩; dsimp only [τF,Purchases.furnace]; rw [ qUses,show saveS C t _ _ _ _ _ _=K _ from congr_fun hK y]; rfl
lemma respects (w:0<t)(p':t≤d) : ∀ᶠ i in L,∀ y, AZ i t y= ¢ i t y:=by
    filter_upwards [tendon H f Y N p j l A z h' Q w p'] with i ⟨V,v'⟩ y; unfold Costume; rw [dif_pos (?_: IsLinearMap ℂ _)]; rfl; let M:= V.comp (standardMap C.labels C (Y i) (N i) (p i) t (r i/ρ i)); rw [show ¢ i t= (( stake r ρ t i • M : Sec G t→ₗ[ℂ] C.label t ) : Sec G t→_) from funext fun t=>congr_arg (_ • ·) (congr_fun v' _) ]; exact LinearMap.isLinear _ -- shadow p!
lemma inflow (v:0<t)(w:t≤d) (x:Toon G t) : CashM L B 1 (fun i=>(C.labels.level t).coeffSize (saveV (C:=C) N p j l ρ t i (streak (Y i) ( Logo G t x) (N i) (p i)))):=by
     obtain ⟨U,H',hK⟩:= Q.enrolls _ v w; exact hK.censusYn h' ( size_le x ) Q.weightJ (Stitch.rep C (Logo G t x)) (study H f Y N p j l A z h' Q x v w)
-- trans to arbitrary fixed.Tag+ horizon vary? fixed. Enough all moving rotations with later theorem.
lemma gearTax (v:0<t)(w:t≤d) (D:ℕ) : CashM L B 1 (stake r ρ D) ∧ CashM L B 1 ( fun i=> ( ↑( r i/ρ i ):ℂ)^D ) := by
    obtain ⟨U,H',h⟩:= Q.enrolls _ v w; let u:= fun i=> r i / ρ i; let x:= fun i=>ρ i/r i; have H:(∀ᶠ i in L,0≤u i ∧ u i≤1 ∧ 0≤x i ∧ x i≤2):=by
        filter_upwards [Q.warm,Q.rise] with i ⟨b,z⟩ ht; unfold u x; have hp:=ht.trans_le b; exact ⟨by positivity,(div_le_one hp).mpr b,by positivity,(div_le_iff₀ ht).mpr z⟩
    constructor
    · refine Wage.enroll (IsBigO.of_bound ((2:ℝ)^D) (?_)); filter_upwards [H] with i ⟨t,h,x,y⟩; unfold stake; rw [norm_pow, Complex.norm_real,Real.norm_of_nonneg x]; exact (pow_le_pow_left₀ x y D).trans_eq (by simp)
    refine Wage.enroll ( IsBigO.of_bound' ( ?_ ) ); filter_upwards [H] with i ⟨t,v,x,w'⟩; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg t, Pi.one_apply,norm_one]; exact pow_le_one₀ t v
lemma paidDet (v:0<t)(w:t≤d) (x:Toon G t): CashM L B 1 (fun i=>(C.labels.level t).coeffSize (saveV (C:=C) N p j l ρ t i (standardV Y N p r ρ (Logo G t x) i))) := by
    let ζ(i):= ( ( ↑ ( r i/ρ i ) ):ℂ)^x.size; let z':= (C.labels.level t).coeffSize; let s := saveV (C:=C) N p j l ρ t; let f'(i):= streak (Y i) (Logo G t x) (N i) (p i); have hp:= (gearTax H f Y N p j l A z h' Q v w x.size).2; -- shadow
    have H1: CashM L B (1:ι→ℝ) (fun i=> ‖ζ i‖ * z' ( s i ( f' i ) )):=by simpa only [mul_one] using Wage.mul (Wage.norm hp) (inflow H f Y N p j l A z h' Q v w x)
    refine Wage.fix H1 ( ?_ ) (.refl ..); filter_upwards [saveOp H f Y N p j l A z h' Q v w] with i ⟨V,hY⟩; unfold standardV; rw [wears, show ∀ a', saveV (C:=C) N p j l ρ t i a'=V a' from congr_fun hY,map_smul,Extra.Histories.Size.smul]; unfold ζ z' s f'; rw [hY] -- shadow
end Motif
end YM.SignedWilsonExpansion.Dancer
