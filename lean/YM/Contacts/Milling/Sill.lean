import YM.Contacts.Milling.Tour
import YM.Contacts.Milling.River
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory Asymptotics
open Finset PertExtension.Series Pulse Pulse.Form Radial Ion YM.Stationary
open scoped Topology BigOperators ContDiff Classical
noncomputable section
variable {α β : Type}[Fintype α][Fintype β]
abbrev House (α:Type) := ℕ→Rack α
variable (F:House α) {n:ℕ}
namespace House
abbrev Dir (α:Type) := α→ℝ
def design {ι:Type}[Fintype ι](F:Field ι α) (x:Dir α):ℝ:= MvPolynomial.aeval x (verse F)
def grate (e r:ℕ) (x:Dir α) := if 2 ≤ e+r then design (F (e+r-2) r) x else 0
def wind (k:ℕ)(j:ℕ) (x:Dir α):= ∑ v∈Finset.range (k-j),grate F j v x
def swell (k:ℕ):= stake (wind F k) k
def terrace (P:House α)(x:Dir α)(e:ℕ):= MvPolynomial.aeval x (stage e (P e))
lemma design_spec {ι:Type}[Fintype ι](f:Field ι α)(x:Dir α): design f x=∑ a:ι→α,f a*∏ j,x (a j):=by simp [verse,design]
lemma design_scale (e r:ℕ)(x:Dir α)(t:ℝ): grate F e r (t• x)=t^r *grate F e r x:= by
  simp_rw [grate]; split; · simp only [design_spec,Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]; simp_rw [mul_sum]; exact sum_congr rfl fun i _=> mul_left_comm ..
  simp
lemma design_ana {ι:Type}[Fintype ι](f:Field ι α)(x:Dir α): AnalyticAt ℝ (design f) x:= by
  apply ContDiffAt.analyticAt; have h : ContDiff ℝ ω (design f) := by simp_rw [show design f=_ from funext (design_spec f)]; fun_prop
  exact h.contDiffAt
lemma grate_ana (e r:ℕ)(x:Dir α): AnalyticAt ℝ (grate F e r) x:= by unfold grate; split; exact design_ana ..; exact analyticAt_const
lemma wind_ana (e r:ℕ)(x:Dir α): AnalyticAt ℝ (wind F e r) x:= by unfold wind; exact ContDiffAt.analyticAt (ContDiffAt.sum (fun i _=> (grate_ana F r i x).contDiffAt)) -- evaluation x vs input at origin ok
lemma wind_jet (k n i:ℕ)(x:Dir α): jet (wind F n k) i x=if i+k<n then grate F k i x else 0:= by
   unfold wind; rw [loan_sum _ (fun _ _=> grate_ana F _ _ 0)]; have h u : jet (grate F k u) i x=if i=u then grate F k i x else 0:= by rw [radiant (grate_ana F k u 0) u i (design_scale F k u)]; split_ifs<;> simp_all
   simp_rw [h]; simp only [Finset.sum_ite_eq, Finset.mem_range]; by_cases hi:i+k<n; · rw [if_pos hi,if_pos (by omega)]
   rw [if_neg hi,if_neg (by omega)]
lemma wind_controls (k n:ℕ): Rung (n-k) (wind F n k):= ⟨funext fun x=>by unfold prepare; refine (Finset.sum_congr rfl fun j hj=> ?_); rw [wind_jet,if_pos (by simp only [Finset.mem_range] at hj; omega)] ⟩
lemma orchestra (k:ℕ): AnalyticAt ℝ (swell F k) 0 := stake_ana fun i _=> wind_ana ..
lemma swell_front (k j:ℕ)(x:Dir α): jet (swell F k) j (1,x)= if j<k then ∑ i∈Finset.range (j+1),grate F i (j-i) x else 0:= by
   unfold swell stake; rw [loan_sum _ (fun i hi=>conjunct_ana (wind_ana F k i 0) i)]
   have he i (hi:i<k): jet (conjunct (wind F k i) i) j ((1:ℝ),x)= if i ≤ j ∧ j<k then grate F i (j-i) x else 0:= by rw [joint _ _ _ _ (wind_ana F _ _ 0),wind_jet]; split_ifs <;> first| rfl| omega| simp_all <;> omega
   split
   next h=> rw [← Finset.sum_subset (f:=fun i=>jet (conjunct (wind F k i) i) j (1,x)) (Finset.range_mono (Nat.succ_le_of_lt h))]; exact sum_congr rfl fun i hi=> (he i (by simp only [Finset.mem_range] at hi; omega)).trans (if_pos ⟨by simp only [Finset.mem_range] at hi; omega,h⟩); intro i hi hb; rw [he _ (mem_range.mp hi),if_neg (by simp only [Finset.mem_range] at hb; omega)]
   next h=> exact sum_eq_zero fun i hi=> (he _ (mem_range.mp hi)).trans (if_neg fun v=>h v.2)
lemma swell_minor (k:ℕ){j:ℕ} (he:j<2)(x:Dir α): jet (swell F k) j (1,x)=0:= by rw [swell_front]; split; refine sum_eq_zero ?_;intro i hi; rw [grate,if_neg (by simp only [Finset.mem_range] at hi; omega)]; rfl
lemma spectrum (k:ℕ): Radial.Stationary (swell F k):= by
   refine ⟨(orchestra F k).contDiffAt, ?_,?_⟩
   · exact jet_zero (swell F k) (1,(0:Dir α)) ▸ swell_minor F k (j:=0) (by decide) _
   intro u; exact (jet_bridge (orchestra F k)).1 (benchPitch (orchestra F k) fun x i hi=>swell_minor F _ hi x) u _ (by decide)
lemma stamp (k e:ℕ)(he:e+2<k)(x:Dir α): jet (swell F k) (e+2) (1,x)= terrace F x e:= by
   rw [swell_front,if_pos he,terrace,stage,map_sum]; -- shift summation
   rw [← Finset.sum_range_reflect (f:=fun i=>grate F i _ x)]
   apply sum_congr rfl; intro j hj; have hz:=Finset.mem_range.mp hj; rw [Nat.add_sub_cancel, show e+2-(e+2-j)= j from by omega,grate,show e+2-j+j=e+2 from by omega, if_pos (by omega),Nat.add_sub_cancel]; rfl
-- remove wind d constants for comp ζ
open Lattice RG Wilson Tree
variable {G:Gauge}{c f nP : Side}
end House
open House Kale
lemma transported {E V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][FiniteDimensional ℝ V]
    {L Y:V→E} {P:ℕ→ E→ℝ} (h:∀ i<n,AnalyticAt ℝ (P i) 0)(hL:AnalyticAt ℝ L 0)(hl:L 0=0)(hY:AnalyticAt ℝ Y 0)(hy:Y 0=0)
    (H:Rays n (stake P n∘ (fun x:ℝ×V=>(x.1,L x.2)) - stake P n∘ (fun x:ℝ×V=>(x.1,Y x.2)))) : ∀ i<n,Rays (n-i) (P i ∘ L - P i ∘ Y):= by
    apply contains; swap; convert H using 1; ext ⟨i,z⟩; simp only [stake,conjunct,Function.comp_apply,Pi.sub_apply, ← Finset.sum_sub_distrib, mul_sub]
    intro i hi; refine (AnalyticAt.comp (g:=P i) (f:=L) ?_ hL).sub (AnalyticAt.comp (g:=P i) (f:=Y) ?_ hY) <;> first| exact hl.symm ▸ h i hi| exact hy.symm ▸ h i hi
open Lattice RG Wilson Tree
variable {G:Gauge}{c f:Side}
lemma wind_guard {M:ℝ→Config G f→Config G c→ℝ} (P:House (Lines G c 1)){T:Ratio c f}(A:Forest T)(ho:Odd T.count.val){b:ℝ}(h:Sight (runner M A) (swell P (n+3)) b n)(hp:Sensor M T): ∀ i<n+3,Guards (wind P (n+3) i) (n+3-i):= by
    let p:=swell P (n+3); let F:=wind P (n+3); have he:=spectrum P (n+3); have hv:=orchestra P (n+3)
    have H u:= buffers A hp hv he h u; have Hs s:=rotates A ho hp hv he h s; have ha i:=wind_controls P i (n+3); have hl i:= wind_ana P (n+3) i 0
    have ht (Q:Link G c →L[ℝ] Link G c) (hq:Rays (n+3) (p-p ∘ axisRoll Q)): ∀ i<n+3,F i ∘ Q=F i := by
       intro i hi; apply Eq.symm (instant (ha _) (repeater (ha _) Q) (show Rays _ _ from transported (P:=F) (L:=id) (Y:=Q) (fun i _=>hl i) analyticAt_id rfl (Q.analyticAt _) Q.map_zero hq i hi))
    intro i hi; refine ⟨continuous_iff_continuousAt.mpr (fun x=>(wind_ana ..).continuousAt),hl _,fun u x=>congr_fun (ht (stain u) (H u) i hi) x,fun s x=> congr_fun (ht (orderTurn s) (Hs s) i hi) x,fun x=> ?_⟩
    have hh:= transported (P:=F) (L:=Prod.snd) (Y:=moveField) (fun i _=>hl i) contDiffAt_snd.analyticAt rfl moveField_analytic moveField_zero (costs_now A hp hv he h) i hi x; refine hh.neg_left.congr_left (fun b=>?_); change -( F i _-F i _)= F i _-F i _; abel
end
end YM.Contacts.Milling
