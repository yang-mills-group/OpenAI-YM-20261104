import YM.LocalLTE.XPre.Gallery
/-!
# Each input ticket.E.Data -> compressed life authority. Keep uncompressed stamp too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter Set MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca Ticket
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι: Type}{G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
    {κ κ' K ν t u q r s b:ℝ} {A:Activities G f} {d t₀ p m l:ℕ} {o:Site f}{o':Site c}
open AbsoluteSums Animals Next.Foundations Source Planned.GuardedAtom
variable {v w:ℂ}{X Y:Wing→Prop}{M:ι→ Leaf R}{g:ι→ℂ}{φ:MergeProof.Response G c}{L:GaugeDoor R C}
variable {E:Config G f→ℂ} {Z: Res G f}{W : Res G c}
set_option quotPrecheck false
local notation "B'"=> localSection G d
local notation "F"=> ((Labels.frames G).level d)
local notation "φB"=> hol G
open Extra.Histories.InputColumn
variable {H:History G} {N n:ℕ} {L:GaugeDoor (H.rep N n (m+1)) (H.rep N n m)}
local notation "s'"=> H.S.side m n
local notation "s"=> H.S.side (m+1) n
local notation "R1"=> H.rep N n (m+1)
local notation "R0"=> H.rep N n m
variable (d) (K: Guard.Keeper ((H.rep N n (m+1)).p) ((H.rep N n (m+1)).activities)) (U: Vinca.Gateway ((Labels.frames G).level d) (hol G) (H.rep N n (m+1)) (H.S.side m n)) (A: Prices)
variable (P:Coefficient ((Labels.frames G).level d) (H.S.side (m+1) n))
local notation "X!'"=> Source.Coefficient F s
local notation "iY"=> (fun i: (F).Index=> Extra.Histories.primary (0:Site s) (Size.axis F i))
local notation "κZ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "κI"=> Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "HX"=> H.S.block m
local notation "v"=> (((HX|>.val):ℂ)^d)
variable (T:Syllabus H N n m (hol G) (rack K P) t) (X' : Coefficient ((Labels.frames G).level d) (H.S.side (m+1) n))
-- needles. D ensure Nonempty.Use with ANY booked Permit. Vinca Key lemma
variable {B: Heading ((Labels.frames G).level d)} {π c' d' w:ℝ}(hD: Vinca.Key (localSection G d) H N n m (hol G) L U c' π w B X)
include hD
variable (i:( (Labels.frames G).level d).Index)(hx:P.x=Size.axis ((Labels.frames G).level d) i)(ha: ∀ i,Y (.gasKey (cart (R:=H.rep N n (m+1)) K i)))(ht:∀ i,X (.gasKey (cart (R:=H.rep N n (m+1)) K i)))(hq:0≤π)
-- old.sens need `Seats`. does not imply revisions but for ∑. discard he.C post.
local notation "Q"=> rack K P
local notation "PF"=> Vinca.coins H N n m φB U Q T i
set_option linter.unusedVariables true
include ht hq
lemma recognized: ∃ t: InputColumn.Listing→ ℝ, (∀ i, (PF i).Format 0 (hol G) R0 ∧ (PF i).remBound 0 (R0) κI (t i)) ∧ Summable t:=by
    let J:=Size.axis F i; let P:= PF
    let z':=c'* (F).coeffSize (Bid.vowel F HX ((F).core J)); let u j:=(R1).p.mass ((Q).support j) (T.a j)
    let t j:=(R1).p.mass ((R1).activities.forced j).support (T.b j); let f j:=π*(t j/κZ); let t' (j : ℕ):ℝ:= if (Q).forced j=0 then 0 else f j
    let τ₀: InputColumn.Listing→ℝ:= consist (if i=0 then 0 else z') (fun i=> π*u i) t'
    have he := Real.sqrt_pos.mpr (Extra.Histories.forcedPos H.levels m)
    have ht' := (T.pier.2.1.div_const κZ).mul_left π; have h : Summable t':= by
        have hp i:0 ≤ f i:=mul_nonneg hq (div_nonneg (T.pier.1 i) (Real.sqrt_nonneg _)); exact ht'.of_nonneg_of_le (fun i => by unfold t';split; exact le_rfl; exact hp _) (fun i=> by unfold t'; split; exact hp _; exact le_rfl)
    refine ⟨τ₀,fun p=> ?_, (added (f:=τ₀) ((T.front.2.1.mul_left π).hasSum) h.hasSum).summable⟩
    rcases p with k|k|k
    · by_cases hi:i=0
      · change let p':= (if i=0 then Vinca.unitP F H n m else U.core i); p'.Format 0 (hol G) (R0) ∧ p'.remBound 0 (R0) κI (if i=0 then 0 else z')
        rw [if_pos hi,if_pos hi]; exact ⟨primary_format («H»:=hol G) _, primary_rem _ he⟩
      unfold Vinca.coins τ₀ consist; simp only [Sum.elim_inl,if_neg hi]
      have h:=(hD.main i hi).cost; exact ⟨h.format,h.bound⟩
    · have h := (hD.regular ((Q).regular k) ((Q).support k) (T.a k) ⟨T.outfit.smooth k,T.outfit.origin k,T.outfit.identity_null k,T.outfit.projects k⟩ (T.fields _)).cost; exact ⟨h.format,h.bound⟩
    unfold Vinca.coins τ₀ t' consist; simp only [Sum.elim_inr]; by_cases hi: (Q|>.forced k)=0
    · rw [if_pos hi,if_pos hi]; exact ⟨primary_format _,primary_rem _ he⟩
    rw [if_neg hi,if_neg hi]; have hp: X (.gasKey k):= by
        have h : k∈ Set.range (cart K):= not_not.mp (fun h=>hi (pit K _ h)); obtain ⟨p,rfl⟩:=h; exact ht _
    let v':= T.force k
    have h :=(hD.forced ((Q).forced k) _ (T.b k) hi hp ⟨T.outfit.invariant k,T.outfit.borel k,T.outfit.supported k,T.outfit.carried k,T.outfit.forcing k⟩ v'.2).cost; exact ⟨h.format,h.bound⟩
end YM.LocalLTE.XPre
