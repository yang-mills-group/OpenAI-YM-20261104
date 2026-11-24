import YM.XSpace.Automatic
import YM.XSpace.Carpet
/-!
# Test arrays through first order & position frame adjusted before taking g-jets
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Retirement
open Function Set Filter Structure1 Cirrus Normalize PowerSeries
open scoped Topology BigOperators Classical
variable {G:Gauge} {d n:ℕ} (W:Initialize G) (V:Store G)(p:Tags G d n)(A:Prediction G d) (m:Mesh)
lemma deposit_live (k:ℕ)(f:Test n) : Deposit m (fun i=> live W d i k p) f=batch W m d k n f p:=by
  let h:∀ i: m.Tuple (n:=n),chartV (⟨m,m.back i,0⟩: Sample n)=i:= Mesh.unback m; rw [Deposit,batches]; simp only [live,h,lite,Finset.mul_sum,Initialize.report_formula,map_sum,map_smul, Finset.smul_sum,smul_eq_mul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; apply Finset.sum_congr rfl; intro j _; rfl
private lemma solo_C (B: FieldEnd G d)(P: Reports G d)(i:ℕ): realm (PowerSeries.C B) P i=recruit B (P i):=by
  ext1 n; ext1 t; ext1 p; let a:Days n:= Finsupp.single none i; have ht(p:Fin n→ Sec G d): pulseU a (PowerSeries.C B) p=B ∘ p:=by ext1 j; simp [a,pulseU,Finsupp.single_eq_of_ne (Option.some_ne_none j)]
  rw [really,recruits, Finset.sum_eq_single a]; rw [ht,show a none=i from Finsupp.single_eq_same]
  · intro b hb he; by_contra ha; apply he; have hh(j:Fin n): b (some j)=0:=by
      by_contra h; apply ha; exact MultilinearMap.map_coord_zero (i:=j) _ (by change coeff (R:=FieldEnd G d) (b (some j)) _ (p j)=_; rw [coeff_C, if_neg h]; rfl)
    ext1 j; cases j with | some j=> rw [hh]; exact Finsupp.single_eq_of_ne (Option.some_ne_none j)|>.symm | none=> have hk:=(totaled b).mp hb; simp_rw [Fintype.sum_option,hh] at hk; simpa [a] using hk
  intro ha; apply False.elim; apply ha; simp [totaled,a]
lemma starting (T:Pick G d)(A:Reports G d): realm (deck T) A 1=recruit (stand (T 0)) (A 1)+tang (stand (T 0)) (T 1).val (A 0):=by
  let C:=stand (T 0); have he:= deviates (deck T) (PowerSeries.C C) A (l:=1) (by norm_num) (fun i hi=> by rw [show i=0 by omega,PowerSeries.coeff_C,if_pos rfl,coeff_zero_eq_constantCoeff_apply,const_deck]); rw [solo_C, pos_decked (n:=1) T one_ne_zero,PowerSeries.coeff_C,if_pos rfl,PowerSeries.coeff_C,if_neg (show (1:ℕ)≠0 from one_ne_zero), show ((T 1).val:FieldEnd G d)-0=(T 1).val by ext1 p; exact sub_zero ((T 1).val p)] at he; exact sub_eq_iff_eq_add.mp he |>.trans (add_comm ..)
def Mix (A B:Point G d n)(V F: FieldEnd G d):= B.compLinearMap (fun _=> V)+ tangentP V F A
lemma mixer (A B:Point G d n)(U X: FieldEnd G d): Mix A B U X p=B (U ∘ p)+∑ i:Fin n,A (update (U ∘ p) i (X (p i))):= congr_arg (_+·) (drawn ..)
lemma mixer_charge (A B:Point G d n)(U H X: FieldEnd G d): Mix A B U X= Mix A (B-lot A H) U (X+H*U):=by
  ext1 x; simp_rw [mixer, sub_apply, lots,LinearMap.add_apply,Module.End.mul_apply, MultilinearMap.map_update_add, Finset.sum_add_distrib, comp_apply]; abel
lemma backs (X U: Change G d): X.val * stand U∈ Change G d:=by
  let Y:=X.val * U.val; have he:Y∈Change G d:=by unfold Y; simp only [may_change,Module.End.mul_apply]; exact ⟨by rw [U.property.1,map_zero],fun l hl p h=>X.property.2.1 l hl _ (U.property.2.1 l hl p h),fun p=> by rw [U.property.2.2.1,X.property.2.2.1],fun s p=> by rw [U.property.2.2.2,X.property.2.2.2]⟩
  rw [stand,mul_add,mul_one]; exact Submodule.add_mem _ X.property he
def batchShift (B:FieldEnd G d): Prediction G d:= batch W m d 1-varies (batch W m d 0) B
def twist (U:Change G d):Change G d:= ⟨_,backs U (V.layout W m d 0)⟩
def uproot (U:Change G d):Change G d:= V.layout W m d 1+twist W V m U
abbrev visor (d:ℕ):= stand (V.layout W m d 0)
lemma payment (U:Change G d): V.opens W m d 1=recruit (visor W V m d) (batchShift W m U.val)+tang (visor W V m d) (uproot W V m U).val (batch W m d 0):=by
  rw [← V.fits_walk, starting]; ext1 n; ext1 f; ext1 p
  simp only [Pi.add_apply,LinearMap.add_apply,add_apply]
  rw [recruits,recruits,batchShift]; simp only [touches,Pi.sub_apply,LinearMap.sub_apply,sub_apply,variation]; simp_rw [uproot,Submodule.coe_add,LinearMap.add_apply, MultilinearMap.map_update_add,Finset.sum_add_distrib];
  let M:= batch W m d 0 n f; let g:= M; simp_rw [twist,Module.End.mul_apply, comp_apply,visor]; abel -- defeq visor & twist

lemma deposit_shift (U:FieldEnd G d)(f:Test n)(F:Mesh → FieldEnd G d)(h:F m=U): Deposit m (fun i=> records W d (F (grab i)) i p) f=batchShift W m U n f p:=by
  unfold records batchShift; simp only [sub_apply,variation,LinearMap.sub_apply,Pi.sub_apply,lots];
  simp_rw [← deposit_live W _ m _ f]; unfold Deposit; simp only [grab,h,mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]; rw [Finset.sum_comm (s:=Finset.univ) (t:=(Finset.univ:Finset (Fin n)))]

def Positioned (d:ℕ)(z: Cirrus.Sample n): Point G d n:= Mix (live W d z 0) (live W d z 1) (visor W V (grab z) d) (V.layout W (grab z) d 1).val
lemma deposit_normal (f:Test n): Deposit m (fun i=> Positioned W V d i p) f= V.opens W m d 1 n f p:=by
  rw [← V.fits_walk,starting]; simp only [Pi.add_apply,LinearMap.add_apply,add_apply,touches,recruits]; simp_rw [← deposit_live W _ m _ f]; unfold Deposit Positioned; simp_rw [mixer,mul_add,Finset.sum_add_distrib, Finset.mul_sum]; rw [Finset.sum_comm (t:=(Finset.univ:Finset (Fin n)))]; rw [mul_add]; simp_rw [Finset.mul_sum]
lemma adapt (z:Cirrus.Sample n)(U:Change G d): Positioned W V d z=Mix (live W d z 0) (records W d U.val z) (visor W V z.F d) (uproot W V z.F U).val:= mixer_charge ..
end YM.XSpace.Retirement
