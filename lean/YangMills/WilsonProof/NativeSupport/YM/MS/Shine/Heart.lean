import YM.MS.Shine.Heart
import YangMills.WilsonProof.NativeSupport.YM.MS.Shine.Perch
/-!
# Peeks and regularity.
 `Live` has common aperture for all ext dimensions and all smearing lists;
 `Exist` manip exact punctured germs. finite evaluation with dimension multiplier omitted.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{b:Bool}{D W:Set ℂ}{R T:ℝ}{c:ℂ}{F H:Mob G}{U:Rip G}{x:ℂ→ℂ}{f g:ℂ→ Mob G} {k:ℤ}
namespace Lift
lemma price (h:Lift f F): kPrice F:= by obtain ⟨g,R,hR,h,he,rfl⟩:= h; exact h.link (mem_ball_self hR) isOpen_ball
lemma wind (h:Lift f F) : Wind f dotty F:= by obtain ⟨g,R,hR,h,he,rfl⟩:= h; exact (Wind.cake h hR).congr he
lemma unique (h:Lift f F)(hp:Lift f H): F=H:= (Lift.wind h).unique (Lift.wind hp)
lemma stays (h:kPrice F): Lift (fun _:ℂ=>F) F:= ⟨ _,1,zero_lt_one, Hol.stays h, EventuallyEq.refl .., rfl⟩ -- `_` location
lemma zero : Lift (0:ℂ→Mob G) 0:= stays (Form0.zero (b:=true)).price
lemma add (h:Lift f F)(hp:Lift g H): Lift (f+g) (F+H):= by obtain ⟨x,s,hs,h,he,rfl⟩:=h; obtain ⟨y,t,ht,hp,hy,rfl⟩:= hp; exact ⟨x+y,min s t,lt_min hs ht,(h.mono (ball_subset_ball (min_le_left ..))).add (hp.mono (ball_subset_ball (min_le_right ..))),(he.add hy),rfl⟩
lemma neg (h:Lift f F): Lift (-f) (-F):= by obtain ⟨x,R,hr,h,hP,rfl⟩:=h; exact ⟨-x,R,hr,h.neg,hP.neg,rfl⟩
lemma sub (h:Lift f F)(hp:Lift g H): Lift (f-g) (F-H):= by simp only [sub_eq_add_neg]; exact Lift.add h (Lift.neg hp)
lemma high (h:Lift f F)(hp:Forest (disc R) x)(hr:0<R): Lift (x • f) (x 0 • F):= by
    obtain ⟨z,s,hz,h,Ht,rfl⟩:=h; exact ⟨ x • z,min s R,lt_min hz hr, (h.mono (ball_subset_ball (min_le_left ..))).rate (fun i hi=> hp i (ball_subset_ball (min_le_right ..) hi)), EventuallyEq.smul (EventuallyEq.refl _ x) Ht,rfl⟩
lemma static (h:Lift f F)(c:ℂ): Lift (c • f) (c • F):= Lift.high (x:=fun _=>c) h (fun _ _=> differentiableAt_const _) zero_lt_one
lemma acre (h:Lift f F){P: Set (Mob G)}(H:Fall (·∈ P))(ht:∀ᶠ i in dotty, f i ∈ P) : F ∈ P:= H (Lift.wind h) ht
lemma spin (h:Lift f F)(hp:∀ᶠ i in dotty, Sturdy b (f i)): ∃ g:ℂ→Mob G,∃ R:ℝ,0<R ∧ Hol (disc R) g ∧ g=ᶠ[dotty] f ∧ g 0=F ∧∀ i∈disc R, Sturdy b (g i):= by
    obtain H:= Lift.acre h (P:=Sturdy b) (Wind.time (b:=b)) hp; obtain ⟨g,R,hR,h,ht,rfl⟩:= h; have hu : {i| Sturdy b (g i)}∈ dotty:= (ht.and hp).mono fun i hi=> hi.1.symm ▸ hi.2; obtain ⟨r,hr,hv⟩:= dotty_mem.mp hu; refine ⟨ _,min r R,lt_min hr hR,h.mono (ball_subset_ball (min_le_right ..)),ht,rfl,fun i hi=>?_⟩; by_cases he:i=0; subst i; exact H; exact hv _ (ball_subset_ball (min_le_left ..) hi) he
lemma plowX (h:Lift f F)(t:ℝ)(z:ℂ): Lift (fun i=> plow z t (f i)) (plow z t F):= by obtain ⟨x,r,hr,h,hK,rfl⟩:=h; exact ⟨ _,r,hr,h.grazes t z,hK.mono (fun i hi=> congr_arg _ hi), rfl⟩
lemma spotX (h:Lift f F)(k:ℤ): Lift (fun i=> spot k (f i)) (spot k F):= by obtain ⟨x,R,hr,h,hK,rfl⟩:=h; exact ⟨_,R,hr,h.spot k,hK.mono (fun i hi=> congr_arg _ hi), rfl⟩
end Lift
namespace Live
lemma stays (h:kPrice F): Live (fun _:ℂ=>F):= ⟨F,Lift.stays h⟩
lemma congr (h:Live f)(he:f=ᶠ[dotty] g): Live g:= by obtain ⟨F,h⟩:=h; exact ⟨ _,Lift.congr h he⟩
lemma tends (h:Live f): ∃ F:Mob G,Wind f dotty F:= by obtain ⟨F,h⟩:=h; exact ⟨F,Lift.wind h⟩
lemma price (h:Live f): ∀ᶠ i in dotty,kPrice (f i):= by obtain ⟨F,x,R,hr,h,hK,hm⟩:=h; exact (hK.and (dotty_bill hr)).mono fun i hi=> hi.1 ▸ (h.link hi.2 isOpen_ball)
lemma zero : Live (0:ℂ→Mob G):= ⟨_,Lift.zero⟩
lemma add (h:Live f)(hp:Live g): Live (f+g):= by obtain ⟨F,h⟩:=h; obtain ⟨H,H⟩:=hp; exact ⟨_,Lift.add h H⟩
lemma sub (h:Live f)(hp:Live g): Live (f-g) := by obtain ⟨F,h⟩:=h; obtain ⟨H,H⟩:=hp; exact ⟨_,Lift.sub h H⟩
lemma neg (h:Live f): Live (-f):= by obtain ⟨F,h⟩:=h; exact ⟨_,Lift.neg h⟩
lemma high (h:Live f)(hp:Forest (disc R) x)(hr:0<R): Live (x • f):= by obtain ⟨F,h⟩:=h; exact ⟨_,Lift.high h hp hr⟩
lemma static (h:Live f)(c:ℂ) : Live (c • f):= by obtain ⟨F,h⟩:=h; exact ⟨_,Lift.static h c⟩
lemma fin (S:Finset I){F:I→ℂ→ Mob G}(h:∀ i∈S,Live (F i)) : Live (∑ i∈S,F i):= by
    classical
    induction S using Finset.induction with
    | empty=> simp only [Finset.sum_empty]; exact Live.zero
    | insert i s hi ih=> rw [Finset.sum_insert hi]; exact Live.add (h i (by simp)) (ih (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
end Live
end YM.MS.Shine
