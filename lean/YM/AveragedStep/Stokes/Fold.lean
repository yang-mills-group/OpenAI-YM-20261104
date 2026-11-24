import YM.AveragedStep.Stokes.Larger
import YM.Tree.Cut
/-! The fine gauge used against the paired output law on each given V is
relative to its lift and on the very forest which removes the slice zero modes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.Loops
open Lattice Wilson RG Function Tree
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)

private lemma stop_box (w:Walk)(x:Cover)(i:Axis):|(stop x w) i-x i|≤w.length:=by
 induction w generalizing x with
 | nil=> simp [stop]
 | cons d w ih=>
   have he:=ih (x+d.vec); simp only [stop,List.length_cons,Nat.cast_add,Nat.cast_one]
   have hd : |(d.vec:Cover) i|≤1:=by unfold Step.vec; split <;> simp <;> split <;> simp
   let a:=stop (x+d.vec) w
   change |a i-x i| ≤ _
   rw [show a i - x i = a i - (x + d.vec : Cover) i + (d.vec:Cover) i from ?_]
   · exact (abs_add_le ..).trans (add_le_add he hd)
   simp only [Pi.add_apply]; abel
private lemma short_closed (x:Site f)(w:Walk)(h:stop x w=x)(hw:2*w.length < f.val):stop (0:Cover) w=0:=by
  have he := wrap_stop_cover (n:=f) (0:Cover) w
  rw [map_zero] at he
  have hp : x+wrap f (stop 0 w)=x+wrap f 0:=by rw [he,map_zero,←stop_add,add_zero,h]
  have hl:=stop_box w (0:Cover)
  refine wrap_injOn f ?_ ?_ (add_left_cancel hp)
  · intro i; simpa using (show -(f.val:ℤ)<2*(stop (0:Cover) w) i ∧ 2*(stop (0:Cover) w) i≤ f.val from by
      have hm:= abs_le.mp (hl i); rw [Pi.zero_apply,sub_zero] at hm; omega)
  intro i; have he :0<(f.val:ℤ):=by positivity
  change -(f.val:ℤ)<2*(0:Cover) i ∧ 2*(0:Cover) i ≤ f.val
  rw [Pi.zero_apply,mul_zero]; exact ⟨by linarith,he.le⟩

def pendant (e:Edge (Site f)): Walk := Lattice.reverse (F.hike e.1)++[posDir e.2] ++ F.hike (e.1+step e.2)
lemma pendant_bound (e:Edge (Site f)):
    List.length (pendant S F e)≤8*S.patch.L.val+1:=by
 simp only [pendant,List.length_append,Lattice.reverse,List.length_reverse,List.length_map,List.length_cons,List.length_nil]
 have h(i):= (F.hike_lower i).trans (F.bound i);
 have ht(i): List.length (F.hike i) ≤ 4*S.patch.L.val:=h i; have h1:=ht e.1; have h2:=ht (e.1+step e.2); omega
lemma pendant_stop (e:Edge (Site f)):stop (S.ratio.embed (S.ratio.parent e.1)) (pendant S F e)= S.ratio.embed (S.ratio.parent (e.1+step e.2)):=by
 unfold pendant; rw [← F.hike_root e.1]; simp_rw [stop_append,reverse_stop,stop,Step.vec_pos,F.hike_root]
lemma pendant_read (e:Edge (Site f))(U:Config G f):travel U (S.ratio.embed (S.ratio.parent e.1)) (pendant S F e)=Lattice.gauge (F.foldAt U) U e:=by
 unfold pendant; rw [← F.hike_root e.1]; simp_rw [travel_append,stop_append,travel_reverse, reverse_stop, travel,stop,Step.vec_pos,Step.pos_read,mul_one]; simp [Lattice.gauge,Forest.foldAt]

/- uniform anchor lift k depending on V; exactly using parent after folding
maintains pins. Since k constant on trunk endpoints, commute this move too. -/
def stamped (x:Site c)(U:Config G f)(V:Config G c):Config G f:=
  Lattice.gauge (strung x V ∘ S.ratio.parent) (Lattice.gauge (F.foldAt U) U)
@[fun_prop] lemma stamp_cont (x:Site c):Continuous fun p:Config G f × Config G c=>stamped S F x p.1 p.2:=by
  unfold stamped Lattice.gauge; fun_prop
lemma stamp_trunk (x:Site c)(U:Config G f)(V:Config G c)(i:↥F.trunks):stamped S F x U V i=1:=by
  unfold stamped
  change strung _ _ _ * Lattice.gauge (F.foldAt U) U i * (strung _ _ _)⁻¹=_
  rw [F.compress U _ i.property,F.trunk_internal i.property,mul_one,mul_inv_cancel]
variable {P:Patch}{K:KernelChoices}
omit S F in
/- pay against raw fine lattice curvature, coarse gauge W=V' nearest
frame and one of the actual normalized noises; no likelihood condition. -/
lemma stamp_price (h:P.Branches K G) :
    ∃ D:ℝ,0≤D∧∃ m:ℕ,∀ (c f:Side) (S:StepData c f) (F:Forest S.ratio), S.patch=P → S.kernel=K →
    20*P.L.val+20<f.val → ∀ e:Edge (Site f),
    let i : Edge (Site c):=(S.ratio.parent e.1,e.2)
    ∃ L:List (Face (Per f)),L.length ≤ m ∧∀ x (U:Config G f) (V:Config G c)(t:S.Choices),
      G.chord (stamped S F x U V e) ≤ D*bill U L+G.chord (setGauge x V i)+G.chord (V i*(S.prediction U t i)⁻¹) := by
  obtain ⟨D,hD,m,H⟩:=native_price P K h
  refine ⟨max D 1,by positivity,m+(9*P.L.val+1)^2,?_⟩
  intro c f S F hP hK hf e i
  subst P K
  let b:=S.ratio.parent (e.1+step e.2)
  by_cases he:b=i.1
  · have ht:=pendant_bound S F e
    have hw:stop (S.ratio.embed i.1) (pendant S F e)=S.ratio.embed i.1:= (pendant_stop S F e).trans (congr_arg _ he)
    obtain ⟨l,hl,T⟩:= closed _ (short_closed _ _ hw (by omega)) (S.ratio.embed i.1)
    refine ⟨l,hl.trans (le_trans (Nat.pow_le_pow_left (show List.length (pendant S F e) ≤ 9*S.patch.L.val+1 from by omega) _) (by omega)),?_⟩
    intro x U V t
    change G.chord (strung x V i.1 * Lattice.gauge (F.foldAt U) U e * (strung x V b)⁻¹) ≤ _
    rw [he,G.chord_conj,← pendant_read]
    apply le_add_of_nonneg_right (G.chord_nonneg _) |>.trans' (le_add_of_nonneg_right (G.chord_nonneg _) |>.trans' ((T G U).trans (le_mul_of_one_le_left (bill_pos ..) (le_max_right ..))))
  have hstep:b=i.1+step e.2:=by
    have hk:= S.ratio.parents_hop S.patch.odd_side e.1 e.2; split at hk; exact hk
    exact (he hk).elim
  let w:=S.repath e.2; let z:=S.ratio.embed i.1
  let q:= pendant S F e ++ Lattice.reverse w
  obtain ⟨l,hl,hN⟩:= H c f S rfl rfl i
  have hv: stop z w=S.ratio.embed b:=by rw [hstep,S.leap]; exact S.stop_repath ..
  have hn: stop z q=z:=by unfold q; rw [stop_append,show stop z (pendant S F e)=S.ratio.embed b from pendant_stop ..,←hv, reverse_stop]
  have hm : List.length q≤9*S.patch.L.val+1:=by
    have hw:=pendant_bound S F e
    rw [show q=pendant S F e++Lattice.reverse (S.repath e.2) from rfl]; simp only [List.length_append,Lattice.reverse,List.length_map,List.length_reverse,StepData.repath,List.length_replicate]; linarith
  obtain ⟨p,hp,T⟩:=closed q (short_closed _ _ hn (by omega)) z
  refine ⟨l++p,List.length_append.le.trans (Nat.add_le_add hl (hp.trans (Nat.pow_le_pow_left hm _))),?_⟩
  intro x U V t
  let E:=Lattice.gauge (F.foldAt U) U e; let Q:=S.prediction U t i; let V':=V i; let A:=travel U z w
  have ht:G.chord (E*A⁻¹)≤bill U p:=by
    have he:=T G U; rw [show q= _ from rfl,travel_append,show stop z (pendant S F e) = _ from pendant_stop S F e,← hv,travel_reverse] at he -- show q rfl wrong
    unfold E; rw [← pendant_read]; exact he
  have hQ:G.chord (Q*A⁻¹) ≤ D*bill U l:=hN U t
  have hz:G.chord (E*Q⁻¹) ≤ max D 1*bill U (l++p):=by
    rw [show E*Q⁻¹=(E*A⁻¹)*(Q*A⁻¹)⁻¹ from by group,bill_append,mul_add,add_comm (max D 1*_)]
    apply (G.chord_triangle _ _).trans (add_le_add (ht.trans (le_mul_of_one_le_left (bill_pos ..) (le_max_right ..))) ?_)
    rw [G.chord_inv]; exact hQ.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (bill_pos ..))
  let a:=strung x V i.1; let d:=strung x V b
  change G.chord (a*E*d⁻¹) ≤ _+G.chord _+G.chord (V'*Q⁻¹)
  rw [show a*E*d⁻¹=(a*(E*V'⁻¹)*a⁻¹)*(a*V'*d⁻¹) by group,show setGauge x V i=a*V'*d⁻¹ from ?_]
  · apply (G.chord_triangle _ _).trans; rw [G.chord_conj,show E*V'⁻¹=E*Q⁻¹*(V'*Q⁻¹)⁻¹ by group,add_right_comm _ (G.chord (a*V'*d⁻¹))]
    have hh:=G.chord_triangle (E*Q⁻¹) ((V'*Q⁻¹)⁻¹); rw [G.chord_inv] at hh
    exact add_le_add_left (hh.trans (add_le_add_left hz _)) _
  unfold setGauge Lattice.gauge d V' a
  rw [hstep]
end YM.AveragedStep.Loops
