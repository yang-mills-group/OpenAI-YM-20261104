import YM.X.Journey.Gob
/-!
# Normalized stamp & periodic covariance interpretation at any center
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate.Fund
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open LiftMark Tensor Rays Hinge
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {n:Side}{k:ℕ}{R:ℝ} {I:Type*} {G:Gauge}
section peri
local notation "Q"=> flow G n
lemma mask_free (u:Lane): milk Q (fireMask u)=fireMask u:= by unfold fireMask beadR; simp only [Finsupp.linearCombination_apply,Finsupp.sum,RCLike.real_smul_eq_coe_smul (K:=ℂ), map_sum,map_smul,dress_fire,milked,color_fire]
variable (w:Lane)(o:Site n)(h:∀ z ∈ w.support, lift (wrap n z)=z)
include h
lemma lift_band {V:Type*}[AddCommGroup V][Module ℝ V](f:Cover→ V): (∑ z:Site n, w (lift z) • f (lift z)) = beadR w f := by
    unfold beadR; rw [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_subset (s₂:=Porch.paisley n)]; swap; · intro i hi; exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,h i hi⟩
    rw [Porch.paisley,Finset.sum_image]; intro i _ j _ hx; exact Function.LeftInverse.injective (g:=wrap n) wrap_lift hx;
    intro i _ hi; rw [Finsupp.notMem_support_iff.mp hi,zero_smul]
-- reflect chamber. prove collector application linear
lemma mask_sweep : hairAt (G:=G) o (fireMask w)=∑ z:Site n, w (lift z) • ∑ i:PlaqAxes,hairAt (z+o) (vertex i):= by
    let L:= ((hairAt o (G:=G)).toLinearMap.restrictScalars ℝ); let f(z:Cover):=∑ i:PlaqAxes,dress z (vertex i:Curly G); have hx:fireMask w=beadR w f:= by unfold fireMask f; simp_rw [dress_fire]
    rw [hx]; change L _=_; rw [beadLm,← lift_band w h]; apply Finset.sum_congr rfl; intro i _; apply congr_arg; unfold comp f; change hairAt (G:=G) o (∑ j:PlaqAxes,dress _ (vertex j))=_; rw [map_sum];simp_rw [tint,wrap_lift]
end peri
variable (q:ℕ+) (χ:Floor R) (S:Finset I) (P:I→ Word G) (i:ℕ) (W:Word G)
local notation "F"=> side q i
local notation "ε"=>epsilon q i
local notation "ℙ"=>flow G (side q i)
variable (x:I→ Site (side q i)){s:Labels.Frames G}
def rebate (B:Bare.Shop s): Curly G:= (epsilon q i)^(-(W.d:ℤ)) • (Bare.raw B W.d 0 (Pert.RawLabels.physicalLabel s W.d (Gravity.billet (q:=q) B W χ i)))
lemma warmedUp (B:Bare.Shop s): warm q B W χ i= milk ℙ (mint ε W 1-rebate q χ i W B- mint ε W 0 * Plate.hollow q W χ i):= by
    rw [map_sub,map_sub]; rw [Plate.warmed];simp_rw [mint,rebate,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_mul_assoc,map_smul,Plate.hollow,gen_pair,mask_free,smul_sub]; rfl
-- expression points. A is still unnormalized.
abbrev payer (S:Finset I)(q:ℕ+)(i:ℕ)(P:I→ Word G)(x:I→ Site (side q i)):= collector S x (fun k=> mint (epsilon q i) (P k) 0)
def neighbor [DecidableEq I](k:I)(B:Bare.Shop s): ℂ:=
    payer (S.erase k) q i P x (hairAt (x k) (mint (epsilon q i) (P k) 1-rebate q χ i (P k) B)) - ∑ z:Site F, ((Floor.maskL q χ i) (lift z)) • (payer S q i P x (∑ j:PlaqAxes,hairAt (z+x k) (vertex j)))
lemma near_word [DecidableEq I](k:I)(hk:k∈ S)(B:Bare.Shop s) (h:∀z∈(Floor.maskL q χ i).support,lift (wrap F z)=z):
    neighbor q χ S P i x k B = payer (S.erase k) q i P x (hairAt (x k) (milk (-ℙ) (warm q B (P k) χ i))):= by
    rw [warmedUp,minus,neighbor]; let f:= fun v:Site F=>∑ j:PlaqAxes,hairAt (v+x k) (vertex j:Curly G); let u:= Floor.maskL q χ i; let Q(k:I):= mint ε (P k) 0; let L:= payer (S.erase k) q i P x; 
    have hu : ∑ z:Site F,u (lift z) • (payer S q i P x (f z))= L (hairAt (x k) (Q k * fireMask u)):= by
       change _= collector (S.erase k) x Q _; rw [map_mul, mask_sweep u (x k) h, Finset.mul_sum,map_sum]; apply Finset.sum_congr rfl; intro j _; rw [show payer S q i P x (f j)=_ from shares S Q x k hk (f j), mul_smul_comm]; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul];rw [mul_comm (f j)]
    simp only [map_sub]; apply congr_arg; exact hu -- sub direction
-- alias path cost. stock translations
local notation "A"=> (atTop:Filter ℕ)
include q
lemma mask_global (hq:1<q.val): ∀ᶠ i in A, ∀z∈(Floor.maskL q χ i).support, lift (wrap (side q i) z)=z:= (spot_lift hq R).mono (fun i hi z h=>hi _ (gate_range R χ.positive.le _ (Floor.tight χ z h)))
-- helper for arbitrary T later; here statement release. Distinct all points R apart. Need r>R so use `exists ∀ finite` later.
variable [DecidableEq I] (y:I→ Fielding.Walk) (p:I→E4) (hp:∀ i∈S,plot q (y i) (p i)) {r:ℝ}(hr:Porch.Apart S p r)(hx:R<r)
include hp hr hx
lemma street_near (hq:1<q.val)(k:I)(hk:k∈S)(B:Bare.Shop s)(z:∀ i:ℕ,Site (side q i)):Released (fun i=> neighbor q χ S P i (stock (fun j:I=>y j i) (z i)) k B):=by
    let f(i):=y i-y k; let a(i):=p i-p k; let L:=fun i=>urban q id (P i) (f i); let t:= S.erase k; have he:0<r:= χ.positive.trans hx; have hi:Set.InjOn a S:= by
       intro i hi j hj h; by_contra hz; have hu:= hr i hi j hj hz; unfold a at h; rw [sub_left_inj] at h; rw [h,sub_self,norm_zero] at hu; linarith
    obtain ⟨g,hg⟩:= near_lap hq t f a (fun i h'=> plot.sub (hp i (Finset.mem_of_mem_erase h')) (hp k hk)) (hi.mono (Finset.coe_subset.mpr (Finset.erase_subset ..))) he.le (fun i h=> hr i (Finset.mem_of_mem_erase h) k hk (Finset.ne_of_mem_erase h)) (g:=L) (fun i _=>urban_cost hq id (f i) (P i)) (Friend.warm_apt hq B χ _ hx) -- args
    refine ⟨g,hg.congr' ?_⟩; filter_upwards [mask_global q χ hq] with i hi; rw [near_word q χ S P i _ k hk B hi]; let Z:= stock (fun j=> y j i) (z i) k; let Y (j):= mint (epsilon q i) (P j) 0; change spine (flow G (side q i)) (fun j=> urban q id (P j) (f j) i) t _ = collector t (stock (fun j=>y j i) (z i)) Y (hairAt Z _); rw [← section_time (fun j=>y j i) (z i) k,hemlock]; simp_rw [mint_urban]; rfl
end YM.PositionX.Crate.Fund
