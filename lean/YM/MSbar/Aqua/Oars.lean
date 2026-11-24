import YM.MSbar.Aqua.Lens
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Aqua
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "K"=>Primary n G
local notation "X"=>Positions (Primary n G)
variable {k p m s:ℕ}{D a b r w C C' B:ℝ}{A:Rep G n}{F:ℝ→ Config G n→ℝ}{f:Nesting G n}
variable (hF:Trend F f A.path A.clip p)(ha:Touch A.eval)
variable (x:Positions (Primary n G))(ρ:Site n→G.Color)
local notation "R"=>film A f r p
local notation "V₀"=>vine A r
local notation "W"=> fun i=> atlas f p i A.path A.clip
variable (hs:∀ i≤p,Stone G i k D B) (hk:∀ i:Body 1 n, ‖tint G _ (r • x) i‖<D)(hV:ContDiffAt ℝ k (vine A r) x)
variable (he:m+1≤ k)(hr:0<r)
include hF ha hs hk hV hr
noncomputable def aim (F:X→ℝ)(ρ:Site n→G.Color)(x:X):= fderiv ℝ F x (grad ρ)
lemma dialect (hX:1 ≤ k) : aim R ρ =ᶠ[𝓝 x] (fun y=> -(costP R (sift ρ 0 r) y + ∑ i∈ Finset.range (p+1), r^i *costP (W i) (sift ρ (p-i) r) y)) :=by
     let Z(i:Body 1 n)(y:X):= ‖tint G _ (r • y) i‖; have ht(i): Continuous (Z i):= continuous_norm.comp ((continuous_apply i).comp ((tint G _).continuous.comp ((r • ContinuousLinearMap.id ℝ X).continuous)))
     filter_upwards [eventually_all.mpr (fun i=> (ht i|>.continuousAt (x:=x)).eventually (eventually_lt_nhds (hk i))), hV.eventually (by simp)] with y h hv; have hv : DifferentiableAt ℝ V₀ y:=hv.differentiableAt (by exact_mod_cast (show k ≠0 from by omega))
     let H': Stone G 0 k D B:=hs 0 (by omega); have he: sift ρ 0 r y=speedsK ρ (r • y)-grad ρ:=by unfold sift Work.G05.blockTaylor; rw [Finset.sum_apply]; simp only [Finset.sum_range_succ, Finset.sum_range_zero,zero_add, Tensor.diagonal,Tensor.coeff_apply_zero,speedStart]; -- names
     exact (wants A f r p hF H'.beam ha y ρ h hv hr.ne').trans (by rw [costP,he]; rfl)
local notation "Z"=> fun i=>sift ρ i r
local notation "I"=> Finset.range (p+1)
include he
lemma boon (l:List K)(hl:l.length=m) : buoy (aim R ρ) x l= - (buoy (costP R (sift ρ 0 r)) x l+∑ i∈Finset.range (p+1), r^i * buoy (costP (W i) (sift ρ (p-i) r)) x l):=by
    let Z' := aim R ρ; have hF':ContDiffAt ℝ k R x:=hV.sub ((Aqua.pure ..).contDiffAt.of_le le_top)
    let Φ(i:ℕ):= costP (W i) (Z (p-i)); let fK:=costP R (Z 0); have hu(i:ℕ)(hi:i≤p):ContDiffAt ℝ m (Z i) x:= (comb ρ i x (hs i hi) _ hk).of_le (by exact_mod_cast (show m ≤ k from by omega)); have hc(i): ContDiffAt ℝ m (Φ i) x:= (((show ContDiffAt ℝ ω (W i) x from (vent ..).contDiffAt)).fderiv_right (by simp)).clm_apply (hu _ (by omega)); have hp: ContDiffAt ℝ m fK x:= (hF'.fderiv_right (by exact_mod_cast he)).clm_apply (hu _ (by omega))
    let H(x:X):= ∑ i∈I, r^i * Φ i x; have hg(i:ℕ): ContDiffAt ℝ m (fun y=> r^i*Φ i y) x:=ContDiffAt.mul contDiffAt_const (hc i); have hx: ContDiffAt ℝ m H x:= ContDiffAt.sum (fun i _=> hg i)
    let hK:= (dialect hF ha x ρ hs hk hV hr (by omega)); let L:= l.map (@bolt K); have hL:L.length≤ m:= by unfold L; rw [List.length_map,hl]
    have hv: aim R ρ =ᶠ[𝓝 x] (fun y=>(-1:ℝ)*(fK y+H y)):= hK.mono (fun y he=> he.trans (neg_one_mul _).symm); unfold buoy
    rw [← show roc _ _ x = roc _ _ _ from (((Lis.follows L hv)|>.eq_of_nhds).symm), wed m L (-1) _ (hp.add hx) hL, neg_one_mul] -- see signature
    congr 1; change roc (fK+H) L x= roc fK L x+_; rw [addedL m L fK H hp hx hL]; congr 1 -- Lis.tot Nat Fin cast.P?
    have ht(t:ℕ) : roc (fun y=> ∑ i∈Finset.range t, r^i*Φ i y) L x= ∑ i∈Finset.range t,r^i * roc (Φ i) L x:=by
       induction t with
       | zero=> simp only [range_zero,sum_empty]; simpa using Lis.wed m L 0 (fun _=> (0:ℝ)) (x:=x) contDiffAt_const hL
       | succ t ih=> simp_rw [Finset.sum_range_succ]; rw [← ih]; refine (addedL m L (fun y=>∑ i∈range t,r^i*Φ i y) (fun y=>r^t * Φ t y) (ContDiffAt.sum (fun i _=> hg i)) (hg t) hL).trans ?_; congr 1; exact wed m L _ _ (hc t) hL
    exact ht (p+1)
-- aux
end YM.MSbar.Aqua
