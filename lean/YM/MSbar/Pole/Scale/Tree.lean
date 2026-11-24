import YM.MSbar.Pole.Scale.Band

/-! # No free integrations. Tree terms enter as genuine integrals at r=0. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Mellin
open Set Function Filter MeasureTheory Momentum Age Ray Ambient
open scoped Topology ContDiff BigOperators Classical Interval
variable {I : Type} [Fintype I] {A : Finset I} {F : ℂ→Cloud I} {R:ℝ} {n:ℕ} {z:ℂ}
local notation "origin" => 𝓝[>] (0:ℝ)
variable (h:Meridian (zone R) F) (hz:z∈zone R) (x:External I n) (d:Age) (hd:d.l=0)
lemma leaf_value {a : Age} (hl:a.l=0) (z:ℂ): a.alpha z=a.a:=by simp [alpha,Age.linear,hl]

-- tree bound after rescaling, input to Mellin
local notation "swing" => fun (i:ℕ) (t:ℝ)=> spill^[i] (augments A n F) z (t,x)
local notation "Job" => Tendsto (fun t:ℝ=>roll A d t F z n x) origin (nhds 0)
include h hz hd
lemma counts (hk : Job) (i:ℕ) (hl : d.a+(i:ℤ)≤0) :
    Tendsto (fun t:ℝ=> (t:ℂ)^(d.increment i z) * swing i t) origin (nhds 0) ∧ swing i 0=0 := by
  induction i with
  | zero=>
    have ht : Tendsto (fun t:ℝ=> (t:ℂ)^(d.increment 0 z) * swing 0 t) origin (nhds 0) := by simpa only [iterate_zero_apply,increment,Nat.cast_zero, add_zero] using! hk
    refine ⟨ht,?_⟩
    let C (t:ℝ):= swing 0 t
    have hh : ContinuousAt C 0 := ((puts h n).stream.smooth (z,(0:ℝ),x) ⟨hz,mem_univ _⟩).continuousAt.comp (f:=fun t:ℝ=>(z,t,x)) (x:=0) (by fun_prop)
    apply tendsto_nhds_unique (hh.continuousWithinAt (s:=Ioi 0))
    let u (t:ℝ):=(t:ℂ)^(-d.increment 0 z)
    by_cases he:d.a=0
    · simpa only [increment,leaf_value hd,he,Nat.cast_zero,Int.cast_zero,add_zero, Complex.cpow_zero,one_mul] using ht
    have hp : 0 < (-d.increment 0 z).re := by simp only [increment,leaf_value hd,Nat.cast_zero,add_zero,Complex.neg_re,Complex.intCast_re]; exact_mod_cast (show (0:ℤ)< -d.a by omega)
    have hr := ((Complex.continuous_ofReal_cpow_const hp).continuousAt (x:=0)).continuousWithinAt (s:=Ioi 0)
    simpa only [mul_zero] using! ((Filter.Tendsto.mul hr ht).congr' (f₂:=C) (by
      filter_upwards [self_mem_nhdsWithin] with t hx
      have he' : (t:ℂ)≠0:=by exact_mod_cast (show 0<t from hx).ne'
      change u t*((t:ℂ)^(d.increment 0 z)*C t)=C t
      rw [show u t=_ from Complex.cpow_neg _ _,inv_mul_cancel_left₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl he'))]))
  | succ i ih=>
    obtain ⟨ht,hp⟩:= ih (by omega)
    let c' := d.increment i z; let b:= d.increment (i+1) z
    have hb: b=c'+1:=by simp [b,c',increment,add_assoc]
    have hs : Tendsto (fun t:ℝ=> (t:ℂ)^b * swing (i+1) t) origin (nhds 0):= by
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with t hu
      have hw : (t:ℂ)≠0:= by exact_mod_cast (show 0<t from hu).ne'
      have he := splitAt (terms Metric.isOpen_ball (puts h n (B:=A)) i) hz t x
      change spill^[i] _ _ (0,x)=0 at hp
      change (t:ℂ)^c'* (spill^[i] _ _ _) = _ * (spill^[i+1] _ _ _); rw [iterate_succ_apply',he,hp,zero_add,hb,Complex.cpow_add _ _ hw, Complex.cpow_one,mul_assoc]
    refine ⟨hs,?_⟩
    let T(t:ℝ):= swing (i+1) t
    have hh : ContinuousAt T 0 := ((terms Metric.isOpen_ball (puts h n (B:=A)) (i+1)).stream.smooth (z,(0:ℝ),x) ⟨hz,mem_univ _⟩).continuousAt.comp (f:=fun t:ℝ=>(z,t,x)) (x:=0) (by fun_prop)
    apply tendsto_nhds_unique (hh.continuousWithinAt (s:=Ioi 0))
    let D := d.a+((i+1:ℕ):ℤ)
    have hB : b= (D:ℂ):=by unfold b D increment; rw [leaf_value hd]; push_cast; ring
    rcases lt_or_eq_of_le hl with hk|hk
    · have hy:D<0:=hk; have he : 0 < (-b).re := by rw [hB,Complex.neg_re,Complex.intCast_re]; exact_mod_cast (neg_pos.mpr hy)
      have hv := (Complex.continuous_ofReal_cpow_const he).continuousAt (x:=0)
      simpa only [mul_zero] using! ((Filter.Tendsto.mul (hv.continuousWithinAt (s:=Ioi 0)) hs).congr' (f₂:=T) (by
        filter_upwards [self_mem_nhdsWithin] with t hu; have hw : (t:ℂ)≠0:=by exact_mod_cast (show 0<t from hu).ne'
        change (t:ℂ)^(-b)*((t:ℂ)^b*T t)=T t; rw [Complex.cpow_neg, inv_mul_cancel_left₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hw))]))
    change D=0 at hk; simpa only [hB,hk,Int.cast_zero,Complex.cpow_zero,one_mul] using hs

lemma child (hk : Job) : Tendsto (fun t:ℝ=> roll A d t (step A d F) z n x) origin (nhds 0):=by
  let s:=d.safety; let P:=pay A d F x z
  have hg : 2 < (d.alpha z).re+s := by
    rw [leaf_value hd,Complex.intCast_re]
    have hh := (Int.cast_lt (R:=ℝ)).mpr (show (2:ℤ) < d.a+ (s:ℤ) by unfold s safety; omega)
    simpa only [Int.cast_add,Int.cast_ofNat,Int.cast_natCast] using hh
  have hp : Continuous P := by
    unfold P pay; apply Continuous.mul _ (Complex.continuous_ofReal_cpow_const <| by simp; linarith)
    exact continuous_iff_continuousAt.mpr fun t=> ((terms Metric.isOpen_ball (puts h n (B:=A)) d.safety).stream.smooth (z,t,x) ⟨hz,mem_univ _⟩).continuousAt.comp (f:=fun t:ℝ=>(z,t,x)) (x:=t) (by fun_prop)
  let Y(i:ℕ)(t:ℝ):= (t:ℂ)^(d.increment i z) * eta A d F i z n x
  have hY(i): Tendsto (Y i) origin (nhds 0):=by
    let D:= d.a+(i:ℤ); rcases le_or_gt D 0 with hv|hv
    · have hh := (counts h hz x d hd hk i hv).2; change pbody A F i z n x=0 at hh; simpa [Y,eta,hh] using (tendsto_const_nhds (x:=(0:ℂ)) (f:=origin))
    have hb:d.increment i z=(D:ℂ):=by unfold D increment; rw [leaf_value hd]; push_cast; rfl
    have hQ : 0 < (d.increment i z).re:= by rw [hb]; exact_mod_cast hv
    have hw:= ((Complex.continuous_ofReal_cpow_const hQ).mul_const (eta A d F i z n x)).continuousAt (x:=0)
    have he : d.increment i z≠0:=by rw [hb]; exact_mod_cast hv.ne'
    simpa only [Complex.ofReal_zero, Complex.zero_cpow he,mul_zero,zero_mul] using! (hw.continuousWithinAt (s:=Ioi 0)|>.tendsto)
  have he:= (intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable 0 0) (hp.stronglyMeasurableAtFilter ..) hp.continuousAt).continuousAt.continuousWithinAt (s:=Ioi 0)
  have hl:= Filter.Tendsto.add he (tendsto_finsetSum (Finset.range d.safety) fun i _ => hY i)
  simp only [intervalIntegral.integral_same,Finset.sum_const_zero,zero_add] at hl
  refine hl.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht; exact (law A h hz x d ht).symm
end YM.MSbar.Pole.Mellin
