import YM.OPE.Compatible.Turbine.Rasp
/-! Linear beam cart exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade Cov Cov.Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I J' : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F: Finset X}
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)(P:Prescription T.sector.derivatives)(u:X)
set_option quotPrecheck false
local notation "L"=> T.sector.derivatives
local notation "K!"=> Arboreal.trim U u
local notation "H"=>brim D (Arboreal.trim U u)
local notation "V"=>brim D U
local notation "Θ"=>glen D U u
variable (p:X→ S.Tag)(hu:u∈ rest U){b d:ℕ}{φ:Filter I}{s:I→X→ℝ}{r f:I→ℝ}
variable [Fintype J'] (z:I→J'→E4)(w:J'→ S.Tag)(t:I→Viewers T)
variable (Y:Burst D U φ r s){η M c:ℝ}(H':Services C Λ S)(hO:Lanes (F:=Λ) T.sector.derivatives) (A: Allot C)(h:P.Coherent)
variable (a:Mode T.sector.derivatives) (hη:0 < η)(hM:0 ≤ M)(hc:0<c) (hh:1 ≤ b)(hb:d ≤ b)
variable (ht:∀ᶠ i in φ, whenHigh U (schedule C b (η/2) (s i))=schedule C b (η/2) (s i) u∧ aperture D C b 2 (η/2) (r i) (s i) u ≤ schedule C b (η/2) (s i) u-1)
variable {x:I→X→E4} (hx:∀ᶠ i in φ,Ridge (s i) η M D U (away (x i) (x i ⊥)))
local notation "O!" => fun i=> x i ⊥
local notation "X!"=> fun i=>away (x i) (x i ⊥)
local notation "Z!"=>fun i=>away (z i) (x i ⊥)
local notation "p₀"=> fun i:V=>(p i.val).1
local notation "K₀"=> fun (n:ℕ) i=> leverage D U p₀ u (s i) d n
local notation "P₀"=> Ward.expose ∘ p
variable (hy:∀ᶠ i in φ, ClearOf (x i ⊥) (z i) c)
local notation "V₀"=> picked V
local notation "P!"=> P.ope
local notation "g"=>fun (b:Mode L) i=> P.ope b (picked Θ (x i)) (picked Θ (Ward.expose∘p)) (x i u)
section Slots
-- step arbitrary variable relative to dependent type cast.
variable [DecidableEq J'] (p':J'→ S.Tag)(i:J')(v:S.Field d)
local notation "K"=> (update (fun j=> (p' j).1) i d)
lemma linearp {m:J'→ℕ} (v:Slots S m) {x:J'→E4} {a:E4}{q:ℝ}(e:Tones T)(h:Covered S q x a):
   ∃ B:S.Field (m i)→ₗ[ℂ]ℂ, ∀ s:S.Field (m i),beam T e q x (update (stockTag v) i (⟨m i,s⟩:S.Tag)) a= B s:=by
   obtain ⟨M,hM⟩:=beam_straight T a m h e
   refine ⟨M.toLinearMap v i,fun s=>Eq.trans (congr_arg (fun f=>beam T e q x f a) ?_) (hM (update v i s))⟩
   ext1 j; by_cases hj:j=i
   · subst j; rw [update_self]; simp only [stockTag,update_self]
   rw [update_of_ne hj]; simp only [stockTag,update_of_ne hj]
lemma linearq (p:J'→ S.Tag) {x:J'→E4} {a:E4}{q:ℝ} (e:Tones T)(h:Covered S q x a) (d:ℕ):
    ∃ B:S.Field d→ₗ[ℂ]ℂ, ∀ s:S.Field d,beam T e q x (update p i (⟨d,s⟩: S.Tag)) a=B s:=by
    let f:= update p i (⟨d,(0:S.Field d)⟩:S.Tag); let n j:=(f j).1; let zz: Slots S n:=fun j=> (f j).2; have he:n i=d:=by simp [n,f]
    -- transport across d. general form
    suffices ∃ B': S.Field (n i)→ₗ[ℂ]ℂ,∀ s:S.Field (n i),beam T e q x (update p i ⟨n i,s⟩) a=B' s by rwa [he] at this
    obtain ⟨B,hB⟩:= linearp T i zz e h; refine ⟨B,fun s=> ?_⟩
    change ∀ s:S.Field (n i),beam T e q x (update f i _) a = _ at hB -- eta
    simpa [f] using hB s
end Slots
lemma paintable {F:Finset X}{u:X}(t:u∈brim D F)(s:S.Tag) [DecidableEq (brim D F)]: picked (brim D F) (update p u s)=update (picked (brim D F) p) (⟨u,t⟩:brim D F) s:=by
    ext1 x; by_cases h:x.val=u
    · obtain rfl := h; rw [show (⟨_,t⟩:brim D F)=x from rfl,update_self]; change update p _ _ x.val = s; rw [update_self]
    rw [update_of_ne (show x ≠ ⟨u,t⟩ from fun e=> h (congr_arg Subtype.val e))]; exact update_of_ne h s p
-- applies to all frontiers
include hη Y in
lemma casing {W:Finset X}(hf:W⊆ U)(hp:Crown W): (∀ᶠ i in φ,Ridge (s i) η M D U (away (x i) (x i ⊥))) → ∀ᶠ i in φ,Covered S (s i ⊥) (picked (brim D W) (x i)) (x i ⊥):=by
    intro hx
    have hu' := Burst.crown D Y; have hr:=(Y.fresh _ hη).fade _ hu'.base
    filter_upwards [hx,(finish_view D Y hx hη hf hp).2,hr.eventually (valid_geometry (S:=S) (I:=↥(brim D W)) M)] with i hi ho hm
    refine hm _ _ ho (fun j=>?_); have hF:= hi.near _ _ hu'.base (brim_under D U W hf j.2) bot_le; unfold away at hF; rw [sub_sub_sub_cancel_right,norm_sub_rev] at hF; exact hF
include hu Y hx hη
lemma prime_cart (w:Tones T) (d:ℕ): ∃ P:I→ S.Field d→ₗ[ℂ]ℂ, ∀ᶠ i in φ,∀ v:S.Field d, frontierCoefficient D T K! w (s i) (x i) (update p u (⟨d,v⟩: S.Tag))=P i v:=by
    have hp:= Burst.crown D Y; have hC:=remains _ hp ((rest_mem ..).mp hu|>.1); have hu':u∈ H := (frontier_trim D U hp ((rest_mem ..).mp hu|>.1) ((rest_mem ..).mp hu|>.2)).2 (Or.inl rfl); let f':H :=⟨u,hu'⟩
    choose! M hM using fun i:I=>(fun h:Covered S (s i ⊥) (picked H (x i)) (O! i) =>linearq T f' (picked H p) w h d)
    refine ⟨M,?_⟩; filter_upwards [casing D Y hη (filter_subset ..) hC hx] with i hi vx
    unfold frontierCoefficient; rw [paintable D p hu']; exact hM i hi vx
-- public fixed beam price for cart
include hM H' A hO
lemma prime_load (c:Tones T) (b:S.Tag): PaidWeight φ r (fun i=> tallInk D U p₀ u (s i) b.fst c.fst) (fun i=> frontierCoefficient D T K! c (s i) (x i) (update p u b)):=by
    have hF:=Burst.crown D Y; let hU':= Burst.heal D Y (filter_subset ..) (remains U hF ((rest_mem ..).1 hu|>.1)); have hw:= solid_beam T D A hO H' hU' (hx.mono fun i hi=> Ridge.heals D (filter_subset ..) _ hi) hη hM (picked H (update p u b)) c
    refine Score.congr hw ?_; filter_upwards with i; refine congr_arg₂ _ ?_ rfl; unfold costed tallInk; refine congr_arg (·/_) ?_; refine Eq.trans ?_ (trimmed_units D P₀ hF hu (Ward.expose b) (s:=s i)); change volume D K! _ _ = volume D K! _ _; unfold volume; apply prod_congr rfl; intro j _; by_cases he:j.val=u
    · change _^((update p u b j.val).1)=_^((pallet P₀ _ u j.val).1); rw [he,pallet,update_self,update_self]; rfl
    change _^((update p u b j.val).1)=_^((pallet P₀ _ u j.val).1); rw [pallet,update_of_ne he,update_of_ne he]; rfl
end YM.OPE.Arboreal.Trace
