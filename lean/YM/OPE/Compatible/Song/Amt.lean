import YM.OPE.Compatible.Song.Veil
/-!
# North. Gauge presence estimate. Clock-relative Mask.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL
variable {i j d k m r l b:ℕ}{n:Side}
variable {I W:Type} {B:I→ Finset (Edge Cover)}{N:I→ Side}{φ:Filter I}{Z:I→ℝ}
variable {M:I→ℕ}(A:Audience φ Z N M r)(f g:GlyphQ G N)(T:I→ Law (Chamber G r))
namespace Shroud
section
private lemma sizedK {X J:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][Fintype J](a:X)(F:Libra.Keys G J→L[ℝ] X)(H:X→ₗ[ℝ] Dual' X)(T:Law (Libra.Keys G J))(hp:SiteL F H T)(x:J×G.ColorIndex→ℝ)(c:ℝ)(hc:0<c)(ht:∀ i,T.P i i≥ c*‖i‖^2)(h:∀ j:J×G.ColorIndex, ‖H (F (PickL G j)) a‖ ≤ x j): ‖pour F H T a‖ ≤ (∑ i,x i)/c:=by
       let f:= H a∘ₗ F.toLinearMap; apply pinL (F:=f) hc ht _ (sum_nonneg (fun i _=>(norm_nonneg _).trans (h i)))
       intro z hZ; change ‖H a (F z)‖ ≤ _; rw [resident z,map_sum,map_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun i _=>?_) ; rw[map_smul,map_smul,norm_smul,hp.hike a]; apply (mul_le_of_le_one_left (norm_nonneg _) _).trans (h i); rw[phone_eq]; exact ((PiLp.norm_apply_le (z i.1) _).trans (norm_le_pi_norm z i.1)).trans hZ -- possible def trunc
-- dynamical any source lens.Separated Proof.F params
private lemma apriori {E:I→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)][∀ i,FiniteDimensional ℝ (E i)] {D:Type}[Fintype D]
       (F:(i:I)→Libra.Keys G D→L[ℝ] E i)(L:(i:I)→ E i→ₗ[ℝ] Dual' (E i))(T:I→Law (Libra.Keys G D))(ht:Tendsto Z φ atTop)
       (hp:∀ᶠ i in φ, SiteL (F i) (L i) (T i))(h:∃ c:ℝ,0 < c ∧∀ᶠ i in φ,∀ x,c*‖x‖^2 ≤ (T i).P x x)(hX:∀ d u,Bills φ Z (fun i x=> L i (F i (PickL G (d,u))) x)):Bills φ Z (fun i x=> pour (F i) (L i) (T i) x) :=by
          obtain ⟨c,hc,H⟩:= h; choose x hx V using fun q:D × G.ColorIndex=> hX q.1 q.2
          let t(i):= (∑ j,x j i)/c; refine ⟨t,?_ ,?_⟩
          · unfold t; simp_rw[div_eq_mul_inv]; exact ((RateLE.sum ht (fun i _=>hx i)).mul (RateLE.const _ ht)).mono (by norm_num)
          filter_upwards [hp,H,eventually_all.mpr V] with i hi hA hC y yK; exact sizedK y (F i) (L i) (T i) hi (fun j=>x j i) c hc hA (fun j=>hC j y yK)
end
variable (h:Shroud A f g T)
include h
set_option maxHeartbeats 200000
omit h in private lemma hatch (F:(i:I) → Chamber G r→L[ℝ] Bid.Dir G (N i))(K:(i:I)→ Bid.Dir G (N i)→ₗ[ℝ] Dual' (Bid.Dir G (N i))) (h:∀ᶠ i in φ,SiteL (F i) (K i) (T i))(ht:Tendsto Z φ atTop)(hp:∃ c:ℝ,0 < c ∧∀ᶠ i in φ,∀ x: Chamber G r,c*‖x‖^2 ≤ (T i).P x x)(hv: ∀ (j:↥(fieldP r))(v:G.ColorIndex), Bills φ Z (fun i y=> K i (F i (PickL G (j,v))) y)): Bills φ Z (fun i x=> pour (F i) (K i) (T i) x):= by
        -- reprove with concrete dims. Reusable.
        obtain ⟨c,hc,H⟩:= hp
        let X:=↥(fieldP r) × G.ColorIndex; choose f hf Y using fun i:X=> hv i.1 i.2; let y(i):=∑ j, f j i; have he:RateLE φ Z y 0:= RateLE.sum (S:=univ) ht (fun i _=>hf i); refine ⟨fun i=>y i*c⁻¹,(he.mul (RateLE.const _ ht)).mono (by norm_num),?_⟩
        filter_upwards [eventually_all.mpr Y,H,h] with i hi hx hd x hv; rw [← div_eq_mul_inv]; exact sizedK x _ _ _ hd (fun j=> f j i) _ hc hx (fun j=>hi j x hv)
omit h in lemma woo (H:(i:I)→Board (N i) (r+1))(V:(i:I)→ Bid.Dir G (N i)→ₗ[ℝ] Dual' (Bid.Dir G (N i)))(h:∀ᶠ i in φ,SiteL (sailT G (H i)) (V i) (T i))(ht:Tendsto Z φ atTop)(hp:∃ c:ℝ,0 < c ∧∀ᶠ i in φ,∀ x: Chamber G r,c*‖x‖^2 ≤ (T i).P x x)(hv:∀ j v,Bills φ Z (fun i (y:Bid.Dir G (N i))=> V i (sailT G (H i) (PickL G (j,v))) y)): Bills φ Z (fun i (x:Bid.Dir G (N i))=> pour (sailT G (H i)) (V i) (T i) x):=by
       let F(i:I):= sailT G (H i); exact hatch T F V h ht hp hv
set_option maxHeartbeats 200000
private lemma axisBill (q : ↥(fieldP r)) (u : G.ColorIndex) : Bills φ Z (fun (i:I) (x:Bid.Dir G (N i))=>VView A f i x q u) :=
  (cohort A f g T h q u).loud
private lemma addressBill (V:(i:I)→Board (N i) (r+1)) (q : ↥(fieldP r)) (u : G.ColorIndex) :
    Bills φ Z (fun (i:I) (x:Bid.Dir G (N i))=>chrom (f i) (sailT G (V i) (PickL G (q,u))) x) :=by
  apply (axisBill A f g T h q u).merge
  exact Filter.Eventually.of_forall (fun i:I =>
    congrArg (fun W : Board (N i) (r+1) => fun x:Bid.Dir G (N i) =>
      chrom (f i) (sailT G W (PickL G (q,u))) x)
      (Subsingleton.elim (A.room i).money (V i)))
private lemma wingν (V:(i:I)→ Board (N i) (r+1)) : Bills φ Z (fun i x=> pour (sailT G (V i)) (chrom (f i)) (T i) x):=
       woo T V (fun i=>chrom (f i)) h.polar A.fair h.rise (addressBill A f g T h V)
lemma beauty :Bills φ Z (fun i x=> ΘT A f T i x):=by unfold ΘT; exact wingν A f g T h _

noncomputable def Frameμ (i:I) : Bid.Dir G (N i) →L[ℝ] Bid.Dir G (N i) :=mate (sailT G (A.room i).money) (chrom (f i)) (T i)
omit h in
private lemma mateB {X E:I→Type}[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℝ (X i)][∀ i,FiniteDimensional ℝ (X i)][∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)][∀ i,FiniteDimensional ℝ (E i)] (F:(i:I)→ X i →L[ℝ] E i) (H:(i:I)→ E i→ₗ[ℝ] Dual' (E i))(T:(i:I)→Law (X i))(ht:Tendsto Z φ atTop)(hv:Bills φ Z (fun i x=>pour (F i) (H i) (T i) x))(hp:∀ i x,‖F i x‖ ≤ ‖x‖): Bills φ Z (fun i x=> mate (F i) (H i) (T i) x):=by
        obtain ⟨b,hb,H'⟩:=hv; exact ⟨_, (RateLE.const 1 ht).add hb ht,H'.mono fun i hi x hx=> (norm_sub_le x _).trans (add_le_add hx ((hp _ _).trans (hi x hx)))⟩
omit h in private lemma roofB (W:(i:I)→ Chamber G r→L[ℝ] Bid.Dir G (N i))(K:(i:I)→ Bid.Dir G (N i)→ₗ[ℝ] Dual' (Bid.Dir G (N i)))(ht:Tendsto Z φ atTop)(hv:Bills φ Z (fun i x=> pour (W i) (K i) (T i) x))(hL:∀ i x,‖W i x‖ ≤ ‖x‖): Bills φ Z (fun i x=> mate (W i) (K i) (T i) x):=by
        obtain ⟨b,hb,H'⟩:=hv; exact ⟨_, (RateLE.const 1 ht).add hb ht,H'.mono fun i hi x hx=> (norm_sub_le x _).trans (add_le_add hx ((hL _ _).trans (hi x hx)))⟩
omit h in lemma Voile (V:(i:I)→ Board (N i) (r+1))(ht:Tendsto Z φ atTop)(hv:Bills φ Z (fun (i:I) (x:Bid.Dir G (N i))=> pour (sailT G (V i)) (chrom (f i)) (T i) x)): Bills φ Z (fun i x=> mate (sailT G (V i)) (chrom (f i)) (T i) x):= roofB T (fun i=>sailT G (V i)) (fun i=>chrom (f i)) ht hv fun _=> sailX G _
lemma polesξ (V:(i:I)→ Board (N i) (r+1)) : Bills φ Z (fun i x=> mate (sailT G (V i)) (chrom (f i)) (T i) x):= Voile f T V A.fair (wingν A f g T h V)
elab "postedBillType% " t:term : term => do
  let v ← Lean.Elab.Term.elabTerm t none
  Lean.Meta.inferType v
lemma poles : postedBillType% (polesξ A f g T h (fun i:I => (A.room i).money)) :=
  polesξ A f g T h (fun i:I => (A.room i).money)
end Shroud
end YM.OPE.Merchant
