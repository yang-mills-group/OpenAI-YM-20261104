import YM.AlbaMS.Odom.Reign

/-!
# Activity for dissertation: normalized half restriction will use Lens

Count consistency proves all type-part projections actually commute (including
prior terms), before any massless limit. Status supports functionals at all orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Inlay.Net.Receipt
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil Lattice
variable {G:Gauge} {V I W J : Type*} [Fintype V][Fintype I][Fintype W][Fintype J]{Ω:Net V I}{H:Net W J}(S: Receipt G Ω H){O:Luster Ω G}{F:Luster H G}
variable (a:ℝ)
structure Meets (S:Receipt G Ω H)(a:ℝ):Prop where
 seats (F:W→ Heave G W J ℝ) : a • (∑ x:V,F (S.parcel x))=∑ w:W,F w
 ghost (F:J→Heave G W J ℝ) : a • (∑ x:I,S.rate x • (S.node x).elim 0 F)=∑ j:J,F j
structure Accord (a:ℝ)(S:Receipt G Ω H)(O:Luster Ω G)(F:Luster H G) : Prop extends Meets S a where
 aura (U): F.integrand U=a*(S.honor O).integrand U
namespace Accord
variable {a S}
lemma bare_eq (h:Accord a S O F): bare (I:=J) F.caseG=a • S.track (bare O.caseG):=by
  rw [← S.honor_track]; unfold bare; rw [← Brook.gleam_smul]; refine (pathof G W J).shadow _ _ ?_; filter_upwards with x; exact h.aura _
lemma memory (h:Meets S a){P:Precision.ChartRatio G}(hp:Precision.LocalRatio P): bare (fragrant hp)= a • S.track (bare (fragrant hp)):=by rw [noted,noted,map_sum]; simp_rw [smiling]; exact (h.seats (sinG hp)).symm
lemma adorned (h: Accord a S O F): superb (grit G J) H.chat (bare F.caseG)= a • S.track (superb (grit G I) Ω.chat (bare O.caseG)):=by rw [whole,whole]; simp_rw [map_sub,map_add,map_sum,S.transmitting,S.transpire, smul_sub,smul_add,h.seats,h.ghost]; rw [h.bare_eq]
end Accord
end YM.MSBar.Inlay.Net.Receipt
namespace YM.MSBar.Odom
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Inlay Inlay.Net Lattice
variable {G:Gauge} {n:Side}(s:Signed)(x:Site n)
abbrev axis (d:Axis):=(posDir d).rotate s
def mande (d:Edge (Site n)) := (axis s d.2).used (affine s x d.1)
lemma mande_stop (d:Edge (Site n)): affine s x (d.1+step d.2)=affine s x d.1+(axis s d.2).vec:=by rw [axis, Step.vec_rotate, Step.vec_pos, affine, s.act_add]; unfold affine; abel
-- signed perm shift same side
lemma mande_inj : Injective (mande s x):=by
  rintro ⟨a,i⟩ ⟨b,j⟩ h; have hh : i=j:= by apply s.perm.injective; have ht:= congr_arg Prod.snd h; unfold mande at ht; simp only [Step.used] at ht; split at ht<;> split at ht<;>exact ht
  subst j; congr 1; unfold mande at h; have ht:=congr_arg Prod.fst h; unfold Step.used at ht; split at ht
  · simp only [sub_left_inj] at ht; exact s.act_injective (add_right_cancel ht)
  exact s.act_injective (add_right_cancel ht)
def conduit (u:G.El): Receipt G (deck n) (deck n) where
 parcel := mande s x
 node i:= some (affine s x i)
 flip i:= (axis s i.2).neg
 color:=u
 rate _:=1
 start e:=by change some (affine _ _ e.1)=_; unfold deck blockN mande Step.used; cases h:(axis s e.2).neg <;> simp
 stop e:=by change some (affine s x (e.1+step e.2))=_; unfold deck blockN mande Step.used; rw [mande_stop,Step.vec]; cases h:(axis s e.2).neg <;> simp [sub_eq_add_neg]
lemma semitrail (g:G.El)(U:Wilson.Config G n): (conduit s x g).react U=Lattice.gauge (fun _=>g) (pull s x U):=by
  ext1 v; unfold Receipt.react conduit pull axis mande Lattice.gauge; simp only [Step.read]
lemma amphora (g:G.El): Receipt.Accord 1 (conduit s x g) (day G n) (day G n) where
 seats F:= by rw [one_smul]; exact Equiv.sum_comp (Equiv.ofBijective (mande s x) ⟨mande_inj ..,(Finite.injective_iff_surjective).1 (mande_inj ..)⟩) F
 ghost F:= by
   change (1:ℝ) • (∑ v:Site n,(1:ℝ) • F (affine s x v))=_; simp_rw [one_smul]; exact Equiv.sum_comp (s.actEquiv.toEquiv.trans (Equiv.addRight x)) F
 aura U:=by rw [one_mul]; change _=Wilson.energy _; rw [semitrail,Wilson.energy_gauge,Wilson.energy_pull]; rfl
end YM.MSBar.Odom
