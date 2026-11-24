import YM.MS.Surgery
import YM.MS.LandauCost
/-!
# The linear-Q part of the cost for closure

Costs the difference of its symbols, not applying the difference to the
lattice-continuum discrepancy until after we've done the closure step. Use all t tapes smooth.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Filter Set Finset Koszul Wire Real
open scoped Topology ContDiff
variable {A P E ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype A] {p : Sector A}
    {w : Wire A E P} {m : A→ℤ} {S : Scale ι}
namespace Charge
lemma delta_cost {b : Bool} (Z Y : Charge p P ℂ) {f : Pool ι A P}
    {a : ι → ℝ} {h : ℤ}
    (ha : ∀ i,0≤ a i) (hp : ∀ i j, Like S.full S a (fun _=>Z.table i j) (fun _=>Y.table i j) fun k _=> S.length k ^ (m i-m j-1))
    (hw : Course b w) (h' : ∀ u : Wire A E P, Course b u → u.length=w.length → Virt S f u h m) :
    Bound S (Chart (fun u=> Z.raise (f u)-Y.raise (f u)) w) fun i=> S.length i ^ (fieldDim m w-(h+1))*a i := by
   have hv : ∀ x, net (sail w x)=net w x:=fun x=>sail_net ..
   unfold Chart; simp_rw [Pi.sub_apply, visit_Z, visit_sail]; simp_rw [← visit_sub, ← Finset.sum_sub_distrib, ← sub_mul]
   refine visit_bound (fun i=> mul_nonneg (zpow_nonneg (S.pos _).le _) (ha i)) (fun l i k H=> ?_)
   refine Costs.sum Finset.univ (fun j _=> ?_) (fun i x _=> mul_nonneg (zpow_nonneg (S.pos _).le _) (ha i))
   let u := (l++(j,i.2)::k); rcases i with ⟨i,q⟩
   have H' : Course b u:= visit_course b l k (i,q) (by rw [H]; exact hw) j
   have Hμ : Virt S f u h m:= h' u H' (by simp [← H,u])
   have Hl : fieldDim m u= fieldDim m w -m i+m j:= by rw [← H]; exact visit_field m l k (i,q) j
   convert (((hp i j).pull q).gain.mul Hμ) using 1
   · ext; simp only [Chart,u,sail_join,sail_cons]
   ext; rw [Hl, mul_right_comm (S.length _ ^ _),← zpow_add₀ (S.pos _).ne']; ring_nf
end Charge
end YM.MS.Plane

namespace YM.MS.Landau
open Function Filter Set Finset Koszul Plane Wire Real Momentum
open scoped Topology ContDiff
open Complex (I)
variable {A C P E ι: Type} [Fintype A] [DecidableEq A] [DecidableEq C]

def send (f:P → Momentum A) : Plane.Charge (parity (A:=A) (C:=C)) P ℂ where
   table := choir (bare (A:=A)) f
   from_opposite a e q hx:= by unfold parity; apply (stamp f).from_opposite _ _ q; rintro h; change bare _ _ _=0 at h; exact hx (by simp [choir,h])

variable {S : Scale ι} {a : ι →ℝ}
omit [DecidableEq A] in
private lemma linear_test (h : ∀ i, 1≤S.length i) (i : A) : Like S.full S (phaseDiff S) (fun _ p=> wave p i) (fun _ p=> p i) fun k _=> (S.length k)⁻¹ := by
    let U := fun i=> (S.length i)⁻¹
    have hZ : Bound S (fun i (_:Momentum A)=> U i) U := Costs.scalar (Cost.of_le fun i p hp=> by change ‖U i‖ ≤ U i; dsimp only [U]; rw [Real.norm_of_nonneg]; exact inv_nonneg.mpr (S.pos _).le)
    have hz := (Like.same (fun i=>(pd_pos i).le) hZ).rmul (omega_check h i)
    convert hz using 1
    · ext; dsimp [spread,U]; field_simp [(S.pos _).ne']
    · ext; dsimp [leaf,U]; field_simp [(S.pos _).ne']
    ext; simp [U]
private lemma quadratic_test (h : ∀ i, 1≤S.length i) (i j : A) : Like S.full S (phaseDiff S) (fun _ p=> precision i j (wave p)) (fun _ p=> precision i j p) fun k _=> phaseDiff S k:= by
    let U := fun i=> (S.length i ^ 2)⁻¹
    have hZ : Bound S (fun i (_:Momentum A)=> U i) U := Costs.scalar (Cost.of_le fun i p hp=> by change ‖U i‖ ≤ U i; dsimp only [U]; rw [Real.norm_of_nonneg]; exact inv_nonneg.mpr (sq_nonneg _))
    convert ((Like.same (fun i=> (pd_pos i).le) hZ).rmul (precision_propagated h i j).1) using 1
    · ext; dsimp [spread,U]; rw [k_scale]; field_simp [(S.pos _).ne']
    · ext; dsimp [leaf,U]; rw [k_scale]; field_simp [(S.pos _).ne']
    ext; simp only [U,mul_one]; rfl
lemma send_cost (h : ∀ i, 1≤ S.length i) (ha : ∀ i, phaseDiff S i ≤ a i) (i j : Leg A C) :
   Like S.full S a (fun _ => (send wave).table i j) (fun _ => (send id).table i j) fun k _=> S.length k ^ (wfield i - wfield j-1):= by
   refine Like.up (a:=phaseDiff S) ?_ ha
   unfold send; dsimp only; unfold choir; split
   · have hh : ∀ s : ℤ, Like S.full S (phaseDiff S) (fun _ (_:Momentum A)=>(0:ℂ)) (fun _ _=>0) (fun i _=> S.length i ^ s):= fun s=> Like.zero (fun i q h=>zpow_nonneg (S.pos _).le _) (fun i=>(pd_pos _).le)
     let K := Complex.ofRealCLM; let I' := ContinuousLinearMap.mul ℝ ℂ I
     rcases i with ⟨⟨_|k,_|_⟩,s⟩ <;> rcases j with ⟨⟨_|l,_|_⟩,t⟩ <;> first | exact hh _ | skip
     · convert! ((linear_test h l).L K).L I' using 1; norm_num [wfield,dim]
     · convert! ((quadratic_test h l k).L K).neg using 1
     · convert! (((linear_test h k).L K).L I').neg using 1; norm_num [wfield,dim]
   exact Like.zero (fun i q h=>zpow_nonneg (S.pos _).le _) (fun i=>(pd_pos _).le)
end YM.MS.Landau
