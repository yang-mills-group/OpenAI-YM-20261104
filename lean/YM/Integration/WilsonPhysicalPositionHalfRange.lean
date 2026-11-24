import YM.Integration.WilsonPhysicalPositionDyadicComposition

/-! The mixed-radius orientation appointment is needed only for adjacent
ratios between one half and one. Iterating the exact physical change gives
the limiting identity on every compact interval of positive ratios. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionHalfRange
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPhysicalPositionReflectedReturn (reading)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

def uniform (d:ℕ)(c:ℝ):Prop:=∀ε:ℝ,0<ε→∀ᶠ r in trail,∀t∈Icc c 1,∀ht:0<t,
    ‖change J d r t ht-ContinuousLinearMap.id ℂ (D d)‖<ε

private theorem smaller {p:ℝ→Prop}(h:∀ᶠ r in trail,p r):∀ᶠ r in trail,∀u:ℝ,0<u→u≤1→p (u*r):=by
  obtain ⟨δ,hd,ball⟩:=Metric.mem_nhdsWithin_iff.mp h
  filter_upwards [Ioo_mem_nhdsGT hd] with r hr u hu h1
  have pos:=mul_pos hu hr.1
  apply ball
  refine ⟨?_,pos⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos pos]
  exact (mul_le_of_le_one_left hr.1.le h1).trans_lt hr.2

private theorem congr_scale {d:ℕ}(r:ℝ){t u:ℝ}(ht:0<t)(hu:0<u)(eq:t=u):
    change J d r t ht=change J d r u hu:=by subst u;rfl

private theorem next (lead:Leading F J)(d:ℕ){c:ℝ}
    (half:uniform J d (1/2))(whole:uniform J d c):uniform J d (c*(1/2)):=by
  have halfpos:0<(1/2:ℝ):=by norm_num
  have halfmem:(1/2:ℝ)∈Icc (1/2) 1:=⟨le_rfl,by norm_num⟩
  obtain ⟨H,hH,control⟩:=WilsonPhysicalPositionDyadicComposition.original J d (1/2) halfpos
  obtain ⟨B,hB,prices⟩:=Frame.comparison F d J lead
  have cap:∀ᶠ r in trail,‖change J d r (1/2) halfpos‖≤B:=by
    filter_upwards [prices (1/2) halfpos] with r paid
    exact ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hB) (paid (1/2) halfmem).1
  intro ε he
  let W:=H*B+2
  have hW:0<W:=by dsimp [W];positivity
  let e:=ε/W
  have ep:0<e:=div_pos he hW
  have wage:H*e*B+e<ε:=by
    have identity:W*e=ε:=mul_div_cancel₀ ε hW.ne'
    calc H*e*B+e < H*e*B+(e+e):=by linarith only [ep]
         _=W*e:=by dsimp only [W];ring
         _=ε:=identity
  have fixed:∀ᶠ r in trail,‖change J d r (1/2) halfpos-ContinuousLinearMap.id ℂ (D d)‖<e:=
    (half e ep).mono fun r h=>h (1/2) halfmem halfpos
  filter_upwards [half ε he,whole e ep,smaller fixed,smaller cap] with r hi prev close frame t ht pos
  by_cases top:(1/2:ℝ)≤t
  · exact hi t ⟨top,ht.2⟩ pos
  let u:=2*t
  have eu:u*(1/2)=t:=by dsimp [u];ring
  have up:0<u:=by dsimp [u];positivity
  have uu:u∈Icc c 1:=⟨by dsimp [u];linarith only [ht.1],by dsimp [u];linarith only [top]⟩
  have bill:=control r u up
  rw [congr_scale J r (mul_pos up halfpos) pos eu] at bill
  refine bill.trans_lt (lt_of_le_of_lt (add_le_add ?_ (le_of_lt (close u up uu.2))) wage)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (prev u uu up).le hH) (frame u up uu.2)
    (ContinuousLinearMap.opNorm_nonneg _) (mul_nonneg hH ep.le)

theorem original (lead:Leading F J)(V:Store G)(d:ℕ):
    ∃v:D d,WilsonPhysicalPositionAdmissible.real C d v=v ∧ ∃γ:ℝ,0<γ ∧
      ((∀ᶠ r in trail,∀t∈Icc (1/2:ℝ) 1,reading F J v r t≤γ)→
      ∀c:ℝ,0<c→uniform J d c):=by
  obtain ⟨v,real,γ,hγ,test⟩:=WilsonPhysicalPositionOnePanel.original F J lead V d
  refine ⟨v,real,γ,hγ,?_⟩
  intro fee c hc
  have base:uniform J d (1/2):=by
    intro ε he
    filter_upwards [test (1/2) (by norm_num) fee ε he] with r ready t ht _
    exact ready t ht
  have ladder(k:ℕ):uniform J d ((1/2:ℝ)^(k+1)):=by
    induction k with
    | zero=>simpa using base
    | succ k ih=>
      rw [pow_succ]
      exact next F J lead d base ih
  obtain ⟨k,hk⟩:=exists_pow_lt_of_lt_one hc (by norm_num : (1/2:ℝ)<1)
  have hcut:(1/2:ℝ)^(k+1)≤c:=by
    rw [pow_succ]
    exact (mul_le_of_le_one_right (by positivity) (by norm_num : (1/2:ℝ)≤1)).trans hk.le
  intro ε he
  filter_upwards [ladder k ε he] with r ready t ht pos
  exact ready t ⟨hcut.trans ht.1,ht.2⟩ pos

end YM.Integration.WilsonPhysicalPositionHalfRange
end
