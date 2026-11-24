import YM.Integration.WilsonHeldExteriorLaw

/-! Changing the action only on an accepted link sheet keeps the complete
old weight of that sheet at each exterior and the weight of every rejected
configuration. The partition of an empty sheet requires no lower bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAcceptedLinkWeight
open Filter Function Set Real MeasureTheory Lattice RG Wilson WilsonHeldExteriorLaw
open private marginal_env total from YM.Integration.WilsonHeldExteriorLaw
open scoped Classical Topology
variable {G:Gauge} {n:Side}
local notation "F" => Config G n

def mass (A:Set (Edge (Site n))) (E:Set F) (p:F→ℝ) (u:Fields G A):ℝ:=
  marginal A (E.indicator p) u

def redraw (A:Set (Edge (Site n))) (E:Set F) (q p:F→ℝ) (U:F):ℝ:=
  let u:=((cut G A) U).1
  let a:=mass A E q u
  let b:=mass A E p u
  if U∈E ∧ b≠0 then (a/b)*p U else q U

@[simp] theorem slice (A:Set (Edge (Site n))) (E:Set F) (q p:F→ℝ) (u:Fields G A):
    mass A E (redraw A E q p) u=mass A E q u := by
  let U:=fun z:Fields G Aᶜ=>(cut G A).symm (u,z)
  have outer (z:Fields G Aᶜ):((cut G A) (U z)).1=u := by simp [U]
  by_cases zero:mass A E p u=0
  · apply integral_congr_ae
    filter_upwards with z
    change E.indicator (redraw A E q p) (U z)=E.indicator q (U z)
    by_cases h:U z∈E <;> simp [Set.indicator,redraw,outer,zero,h]
  · let m:=mass A E q u / mass A E p u
    have equal (z:Fields G Aᶜ):E.indicator (redraw A E q p) (U z)=m*E.indicator p (U z):=by
      by_cases h:U z∈E <;> simp [Set.indicator,redraw,outer,zero,h,m]
    calc
      _=∫z,m*(E.indicator p (U z)) ∂sheet G Aᶜ:=integral_congr_ae (ae_of_all _ equal)
      _=m*mass A E p u:=integral_const_mul _ _
      _=_:=div_mul_cancel₀ _ zero

private theorem indicator_env {E:Set F}(e:MeasurableSet E){p:F→ℝ}(hp:Envelope p):Envelope (E.indicator p):=by
  obtain ⟨C,b⟩:=hp.cost
  have c:0≤C:=(norm_nonneg _).trans (b 1)
  refine ⟨hp.meas.indicator e,C,fun U=>?_⟩
  by_cases h:U∈E
  · rw [Set.indicator_of_mem h]; exact b U
  · rw [Set.indicator_of_notMem h,norm_zero];exact c

private theorem inner {A:Set (Edge (Site n))}(u:Fields G A){f:F→ℝ}(h:Envelope f):
    Integrable (fun z:Fields G Aᶜ=>f ((cut G A).symm (u,z))) (sheet G Aᶜ) := by
  have h':Envelope (fun z:Fields G Aᶜ=>f ((cut G A).symm (u,z))) :=
    ⟨h.meas.comp ((cut G A).symm.measurable.comp (measurable_const.prodMk measurable_id)),
      h.cost.imp fun _ b z=>b _⟩
  exact h'.integrable _

/-- A pairwise bound is needed only between accepted fields with the same
actual exterior. The right side vanishes pointwise off that sheet. -/
theorem variation (A:Set (Edge (Site n))) (E:Set F) (e:MeasurableSet E)
    (q p J:F→ℝ) (hq:Envelope q) (hp:Envelope p) (qn:∀U,0≤q U)
    (factor:∀U∈E,p U=q U*exp (J U)) {δ:ℝ} (nonneg:0≤δ)
    (osc:∀U∈E,∀V∈E,((cut G A) U).1=((cut G A) V).1→|J U-J V|≤δ) :
    ∀U,|redraw A E q p U-q U|≤(exp δ-1)*E.indicator q U := by
  intro U
  let u:=((cut G A) U).1
  let a:=mass A E q u
  let b:=mass A E p u
  have big:0≤exp δ-1:=sub_nonneg.mpr (one_le_exp nonneg)
  by_cases inside:U∈E
  · rw [Set.indicator_of_mem inside]
    by_cases zero:b=0
    · have eq:redraw A E q p U=q U:=by simp [redraw,u,b,inside,zero]
      rw [eq,sub_self,abs_zero];exact mul_nonneg big (qn U)
    let U' (v:Fields G Aᶜ):F:=(cut G A).symm (u,v)
    have outer (z:Fields G Aᶜ):((cut G A) (U' z)).1=u:=by simp [U']
    let q':=E.indicator q
    let p':=E.indicator p
    have pq (z:Fields G Aᶜ):0≤q' (U' z):=by by_cases h:U' z∈E <;>simp [q',h,qn]
    have bounds (z:Fields G Aᶜ):
        q' (U' z)*exp (J U-δ) ≤p' (U' z) ∧ p' (U' z)≤q' (U' z)*exp (J U+δ) := by
      by_cases h:U' z∈E
      · have pair:=abs_le.mp (osc U inside (U' z) h (outer z).symm)
        simp only [q',p',Set.indicator_of_mem h,factor _ h]
        exact ⟨mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (qn _),
          mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (qn _)⟩
      · simp [q',p',h]
    have qi:=inner u (indicator_env e hq)
    have pi:=inner u (indicator_env e hp)
    have lo:a*exp (J U-δ)≤b := by
      have v:=integral_mono (qi.mul_const (exp (J U-δ))) pi (fun z=>(bounds z).1)
      rw [integral_mul_const] at v
      unfold a b mass marginal
      exact v
    have hi:b≤a*exp (J U+δ) := by
      have v:=integral_mono pi (qi.mul_const (exp (J U+δ))) (fun z=>(bounds z).2)
      rw [integral_mul_const] at v
      unfold a b mass marginal
      exact v
    have aa:0≤a:=integral_nonneg pq
    have bp:0<b:=lt_of_le_of_ne ((mul_nonneg aa (exp_pos _).le).trans lo) (Ne.symm zero)
    have e₁:a*exp (J U)≤exp δ*b:=by
      calc _=exp δ*(a*exp (J U-δ)):=by rw [mul_left_comm,←exp_add];ring_nf
           _≤_:=mul_le_mul_of_nonneg_left lo (exp_pos _).le
    have e₂:exp (-δ)*b≤a*exp (J U):=by
      calc _≤exp (-δ)*(a*exp (J U+δ)):=mul_le_mul_of_nonneg_left hi (exp_pos _).le
           _=_:=by rw [mul_left_comm,←exp_add];ring_nf
    let r:=a*exp (J U)/b
    have rlo:exp (-δ)≤r:=(le_div_iff₀ bp).mpr e₂
    have rhi:r≤exp δ:=(div_le_iff₀ bp).mpr e₁
    have inv:1-exp (-δ)≤exp δ-1:=by linarith only [Real.add_one_le_exp δ,Real.add_one_le_exp (-δ)]
    have fine:|r-1|≤exp δ-1:=abs_le.mpr ⟨by linarith,by linarith⟩
    have eq:redraw A E q p U=q U*r:=by
      change (if U∈E ∧ b≠0 then (a/b)*p U else q U)=_
      rw [if_pos ⟨inside,zero⟩,factor U inside]
      dsimp only [r];ring
    rw [eq,←mul_sub_one,abs_mul,abs_of_nonneg (qn U),mul_comm]
    exact mul_le_mul_of_nonneg_right fine (qn U)
  · simp [redraw,inside]

theorem full (A:Set (Edge (Site n))) (E:Set F) (e:MeasurableSet E) (q p:F→ℝ)
    (hq:Envelope q) (hp:Envelope p) {δ:ℝ} (d:0≤δ)
    (bound:∀U,|redraw A E q p U-q U|≤δ*E.indicator q U) :
    Envelope (redraw A E q p) ∧
    ∀u,marginal A (redraw A E q p) u=marginal A q u := by
  let w:=redraw A E q p
  have mp:Measurable (mass A E p):=(marginal_env A (indicator_env e hp)).meas
  have mq:Measurable (mass A E q):=(marginal_env A (indicator_env e hq)).meas
  have ou:=measurable_fst.comp (cut G A).measurable
  have wm:Measurable w:=((mq.comp ou).div (mp.comp ou)).mul hp.meas |>.ite
    (e.inter (((mp.comp ou) (measurableSet_singleton (0:ℝ))).compl)) hq.meas
  obtain ⟨C,cap⟩:=hq.cost
  have c:0≤C:=(norm_nonneg _).trans (cap 1)
  have hW:Envelope w:=by
    refine ⟨wm,(δ+1)*C,fun U=>?_⟩
    have hu:E.indicator q U≤C:=by
      by_cases h:U∈E
      · rw [Set.indicator_of_mem h];exact (le_abs_self _).trans (cap U)
      · rw [Set.indicator_of_notMem h];exact c
    have led:=le_trans (bound U) (mul_le_mul_of_nonneg_left hu d)
    change |w U|≤_
    have tri:|w U|≤|w U-q U|+|q U|:=by simpa only [sub_add_cancel] using abs_add_le (w U-q U) (q U)
    calc _≤|w U-q U|+|q U|:=tri
         _≤δ*C+C:=add_le_add led (cap U)
         _=(δ+1)*C:=by ring
  refine ⟨hW,fun u=>?_⟩
  have dis (v:F):w v=E.indicator w v+Eᶜ.indicator q v:=by by_cases h:v∈E <;> simp [w,redraw,h]
  have qi (v:F):q v=E.indicator q v+Eᶜ.indicator q v:=by by_cases h:v∈E <;>simp [Set.indicator,h]
  have rest:=inner u (indicator_env e.compl hq)
  have one:marginal A w u=mass A E w u+mass A Eᶜ q u:=by
    let U:=fun v:Fields G Aᶜ=>(cut G A).symm (u,v)
    calc
      _=∫v,E.indicator w (U v)+Eᶜ.indicator q (U v) ∂sheet G Aᶜ:=integral_congr_ae (ae_of_all _ fun v=>dis (U v))
      _=_:=integral_add (inner u (indicator_env e hW)) rest
  have two:marginal A q u=mass A E q u+mass A Eᶜ q u:=by
    let U:=fun v:Fields G Aᶜ=>(cut G A).symm (u,v)
    calc
      _=∫v,E.indicator q (U v)+Eᶜ.indicator q (U v) ∂sheet G Aᶜ:=integral_congr_ae (ae_of_all _ fun v=>qi (U v))
      _=_:=integral_add (inner u (indicator_env e hq)) rest
  rw [one,two,slice]

end YM.Integration.WilsonAcceptedLinkWeight
end
