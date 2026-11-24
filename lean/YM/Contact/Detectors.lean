import YM.Contact.Orbits
import YM.Contact.Splitting

/-! Fixed physical detectors:
choose once a finite injective list of centered, strictly separated Wilson evaluations at each
horizon and a linear reconstruction, then average over the compact rotation group and the real
structure. Pull the whole placement back before each cluster projection; average the *field
output*, not a new choice of labels for each test. No UV matching premise follows just from existence. -/

noncomputable section
set_option autoImplicit false
open LinearMap Set Filter Function MeasureTheory TopologicalSpace
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
namespace YM.Contacts
open scoped Contacts
variable {G:Gauge}{L:Register G}(S:Table L) (d:ℕ)
variable {X:Type*}

lemma value_continuous [TopologicalSpace X] {m:ℕ} (T:Table L)(h:T.Smooth) (t:Caps m) (x:X→Points m) (hx:Continuous x) (hc:∀ u,x u∈conf m)
   (v:X→(j:Fin m)→S.Field (t j))(hv:∀ j, Continuous fun u=>v u j):
    Continuous (fun u=> S.classMoment T t (x u) (v u)):=by
  classical
  let b(j:Fin m):= Module.Free.chooseBasis ℂ (S.Field (t j))
  let ι(j:Fin m) := Module.Free.ChooseBasisIndex ℂ (S.Field (t j))
  letI: ∀ j,Fintype (ι j):=fun _=> inferInstanceAs (Fintype (Module.Free.ChooseBasisIndex ℂ _)); let b' (j):Module.Basis (ι j) ℂ (S.Field (t j)):=b j
  let a (r:Π j,ι j) (j):= b' j (r j)
  let gh(y) (r : Π j,ι j):=∏ j,(b' j).coord (r j) (v y j)
  have ht (u:X):v u =fun j=> ∑ k:ι j,(b' j).coord k (v u j) • b' j k:=funext fun j=> ((b' j).sum_repr _).symm
  have he(y:X):S.classMoment T t (x y) (v y) = ∑ r: Π j,ι j,gh y r • S.classMoment T t (x y) (a r):=by
    rw [ht, MultilinearMap.map_sum]; refine Finset.sum_congr rfl fun r _=> MultilinearMap.map_smul_univ ..
  simp_rw [he]
  exact continuous_finsetSum _ fun r _=> (continuous_finsetProd _ fun j _=> ((b' j).coord (r j)).continuous_of_finiteDimensional.comp (hv _)).mul ((S.class_smooth T h (fun j=>⟨t j,a r j⟩)).continuousOn.comp_continuous hx hc)

lemma value_smooth [NormedAddCommGroup X][NormedSpace ℝ X] {m:ℕ} (T:Table L)(h:T.Smooth) (t:Caps m) (x:X→Points m) {s:Set X} (hx:ContDiffOn ℝ ∞ x s) (hc:∀ u∈s,x u∈conf m)
   (v:X→(j:Fin m)→S.Field (t j))(hv:∀ j, ContDiffOn ℝ ∞ (fun u=>v u j) s):
    ContDiffOn ℝ ∞ (fun u=> S.classMoment T t (x u) (v u)) s:=by
  classical
  let ι(j:Fin m) := Module.Free.ChooseBasisIndex ℂ (S.Field (t j))
  letI: ∀ j,Fintype (ι j):=fun _=> inferInstanceAs (Fintype (Module.Free.ChooseBasisIndex ℂ _)); let b' (j):Module.Basis (ι j) ℂ (S.Field (t j)):= Module.Free.chooseBasis ..
  let a (r:Π j,ι j) (j):= b' j (r j)
  let gh(y)(r:Π j,ι j):ℂ:=∏ j,(b' j).coord (r j) (v y j)
  have ht (u:X):v u =fun j=> ∑ k:ι j,(b' j).coord k (v u j) • b' j k:=funext fun j=> ((b' j).sum_repr _).symm
  have he(y:X):S.classMoment T t (x y) (v y) = ∑ r: Π j,ι j,gh y r • S.classMoment T t (x y) (a r):=by
    rw [ht, MultilinearMap.map_sum]; refine Finset.sum_congr rfl fun r _=> MultilinearMap.map_smul_univ ..
  simp_rw [he]
  refine ContDiffOn.sum fun r _=> ContDiffOn.mul (show ContDiffOn ℝ ∞ (fun y:X=>gh y r) _ from ?_) (show ContDiffOn ℝ ∞ (fun y:X=> S.classMoment T t (x y) (a r)) _ from ?_)
  · let w j := LinearMap.toContinuousLinearMap (((b' j).coord (r j)).restrictScalars ℝ)
    have hf (j):ContDiffOn ℝ ∞ (fun y=>w j (v y j)) s:=(w j).contDiff.comp_contDiffOn (hv j)
    suffices he:∀ Z:Finset (Fin m), ContDiffOn ℝ ∞ (fun y=>∏ j∈Z,w j (v y j)) s from he Finset.univ
    intro Z; induction Z using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty]; exact contDiffOn_const
    | insert i Z hi ih=> simp only [Finset.prod_insert hi]; exact (hf i).mul ih
  exact (S.class_smooth T h (fun j=>⟨t j,a r j⟩)).comp hx hc

/-- Finite list of base-hierarchy `Exterior L` testing arrangements fixing the centroid. -/
structure Foci where
   index : Type
   fintypeFoci : Fintype index
   shell : index→Exterior L
   rooted (i): (shell i).point 0=0
   decoder : (index→ℂ)→ₗ[ℂ] S.Field d
   detects v : decoder (fun i=> S.spectra d v (shell i))=v
attribute [instance] Foci.fintypeFoci

namespace Foci
variable {S d}

private def centered (w:Exterior L) : Exterior L:=⟨w.n,Points.across (-w.point 0) w.point,w.letter,Points.across_in _ w.clear⟩
private def sample (u : Exterior L) (i:ℕ): S.Field i→ₗ[ℂ] ℂ := (LinearMap.proj (centered u)).comp (S.spectra i)

lemma available (HS:S.Homogeneous) (d:ℕ): Nonempty (Foci S d):= by
  classical
  letI : ProperSpace (S.Field d):= FiniteDimensional.proper ℂ _
  letI : Nontrivial E4:= inferInstance
  let U(w:Exterior L):= {v:S.Field d|sample (S:=S) w d v≠0}
  have hev (w v): S.spectra d v w= sample (S:=S) w d v:=by
     obtain ⟨p,rfl⟩:= S.onto _ v
     exact (HS _ w.point w.clear _ (Fin.cons ⟨d,p⟩ w.letter)).symm
  obtain ⟨rows,hrows⟩:= (isCompact_sphere (0:S.Field d) 1).elim_finite_subcover U (fun w=>isOpen_ne_fun (sample w d|>.continuous_of_finiteDimensional) continuous_const)
       (fun a ha=> by
          have hz: ‖a‖=1:=(dist_zero_right _).symm.trans (Metric.mem_sphere.mp ha)
          have hne: S.spectra d a ≠ 0:=by intro h; exact (ne_of_apply_ne _ (show ‖a‖≠‖(0:S.Field d)‖ by simp [hz])) (S.faithfully d (h.trans (map_zero (S.spectra d)).symm)) -- simpler
          obtain ⟨u,h⟩:=Function.ne_iff.mp hne
          exact Set.mem_iUnion.mpr ⟨u,by simpa [U,←hev] using h⟩)
  let T': S.Field d→ₗ[ℂ] (rows→ℂ):= LinearMap.pi fun i=> sample i.val d
  obtain ⟨q,hq⟩:= exists_leftInverse_of_injective T' (ker_eq_bot'.mpr fun a ha=>by
     by_contra hn; have hn:= norm_pos_iff.mpr hn; let v:= ‖a‖⁻¹ • a; have hv:v∈Metric.sphere 0 1:= by dsimp [v]; rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hn|>.le), inv_mul_cancel₀ hn.ne']
     obtain ⟨i,h,he⟩:= mem_iUnion₂.mp (hrows hv)
     have hh:= congr_fun ha (⟨_,h⟩:↥rows)
     exact he (by dsimp only [v]; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul, (show sample (S:=S) i d a=0 from hh),smul_zero]))
  refine ⟨⟨↥rows,inferInstance,fun i=>centered i,(by intro i; change (↑i: Exterior L).point 0+(-(i.val:Exterior L).point 0)=0; exact add_neg_cancel _),q,fun v=>?_⟩⟩
  exact LinearMap.congr_fun hq v

variable (D:Foci S d){k:ℕ}
def clearance := Finset.inf' Finset.univ Finset.univ_nonempty (fun u : Option ((i:D.index) × Fin (D.shell i).n)=> u.elim 1 fun x=> ‖Points.tail (D.shell x.1).point x.2‖)
lemma clearance_pos: 0<D.clearance:=by
  refine (Finset.lt_inf'_iff _).mpr fun i hi=> ?_; cases i with
  | none=> exact zero_lt_one
  | some i=>exact norm_pos_iff.mpr (fun hh=> (show Fin.succ i.snd=0 from (D.shell i.1).clear (Eq.trans hh (D.rooted i.1).symm))|>i.snd.succ_ne_zero)
lemma clearance_le (i:D.index)(j:Fin (D.shell i).n): D.clearance≤ ‖Points.tail (D.shell i).point j‖:=by
  exact @Finset.inf'_le ℝ (Option ((i:D.index) × Fin (D.shell i).n)) _ Finset.univ (fun u : Option ((i:D.index) × Fin (D.shell i).n)=> u.elim 1 fun x=> ‖Points.tail (D.shell x.1).point x.2‖) (some ⟨i,j⟩) (Finset.mem_univ _)
end Foci
end YM.Contacts
