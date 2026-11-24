import YM.RegulatorIR.Halo.Shift

/-!
# Auxiliary translated cluster journey

These constructs are independent of the Taylor/calibration meaning and size of
the source data. Need full `Coverage` and `Preserved` and more on physical use. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Sight
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge} {W:Type}{M:W→ℕ}{n:Page M→Side}
variable {S: Heir n G} (H:Reel S)
section Supports
variable (T:S.Accounts)
-- demands derivable algebraically from genuine primitive
include H
lemma natural_o (w:Flap M) i j: (Step.combine (S.maps w.prev) (S.maps w.next)).Ready ((S.frames w).addon i j) := by
 obtain ⟨p,h,hp⟩:= H.powers w; rw [hp,H.realms,H.realms]; exact (Prim.cosmos _ _ _ (H.teeth w) _ _ _ _ h).novel i j
lemma essential (w:Flap M) : Vacuum ((S.frames w).addon):=by
 obtain ⟨p,h,hp⟩:=H.powers w; rw [hp];exact (Prim.cosmos (F:=H.forest w) (T:=p) _ _ (H.teeth w) (H.even _) (H.phase w.prev) (H.even _) (H.phase w.next) h).grammar
lemma suitable (w:Flap M) : Layer.Sym (Step.combine (S.maps w.prev) (S.maps w.next)) (Step.combine (S.maps w.prev) (S.maps w.next)) ((S.frames w).driftL):= by rw [H.meanF];exact fun d x y=> Terrain _ _ _ (H.moduli w).sym.2.2.1 d y x
lemma hort (w:Flap M) : Layer.Sym (Step.combine (S.maps w.prev) (S.maps w.next)) (Step.combine (S.maps w.prev) (S.maps w.next)) ((S.frames w).line):= by rw [H.bondF];rintro d (i|i) (j|j) <;> first|exact (H.moduli w).sym.2.2.2 d i j | rfl
variable (HH:H.Follows T)
include HH
lemma helium :∀ w i j,(S.maps w).Ready (T.bulk w i j):=by
 apply Page.proves
 · intro w i j;obtain ⟨v,h,hv,hg⟩:= HH w;rw [hv,H.realms]; exact (Prim.ark _ _ _ h).novel i j
 intro w hs i j; rw [← T.step_v w]; let f:=S.frames w; unfold GridStep.pure;split;exact ready_zero _
 apply Channel.crop_valid; apply draft_ready _ (suitable H w)
 unfold ceaseHeat heated; refine ready_sum _ _ fun k _=> ?_
 exact Uniform.heat_uses (S.lifts.room w) f.line (f.jVac (T.bulk w.prev)) (hort H w) (fun p (hp:p ≤ i) j=>ready_add _ (Channel.offer_valid (firstChannel ..) (hs p j)) (natural_o H w p j)) false k i j le_rfl
lemma alloy (w:Flap M) i j:(S.lifts.room w).Ready ((S.frames w).jVac (T.bulk w.prev) i j):= ready_add _ (Channel.offer_valid _ (helium H T HH w.prev i j)) (natural_o H w i j)
end Supports

-- paging driver by steps in Page

def seriesC {X: Page M→ Type}(P:∀ w, X (Page.opening M w))(R:∀ i:Flap M,X i.prev→X i.next)(j:Page M): X j:= pass j.bindW j.downW j.good
where
 pass : ∀ w:W,∀ k (h:k≤ M w),X ⟨w,k,h⟩
 | w,0,_=>P w
 | w,k+1,h=>R (⟨w,k,h⟩:Flap M) (pass w k (by omega))
lemma earlierC {X: Page M → Type} {P:∀ w,X (Page.opening M w)}{R:∀ i:Flap M,X i.prev→X i.next}(w): seriesC P R (Page.opening M w)=P w:= rfl
lemma laterC {X:Page M→Type} {P:∀ w,X (Page.opening M w)}{R:∀ i:Flap M,X i.prev→X i.next}(w): seriesC P R w.next=R w (seriesC P R w.prev):=by cases w with| mk w k h=> exact seriesC.pass.eq_2 ..

section Vacuum
variable (T:S.Accounts)(w:W)
local notation "E" => eternal H w
local notation "i₀" => Page.opening M w


def singer (z:Side) : Orders (Book G (Sight.slab z * n i₀)):=fun e r=>(radar H w (Page.opening (extent M w) z)).deckSum (T.bulk i₀ e r)

def tele : (eternal H w).Accounts:= {
 bulk:= fun i=>T.bulk (Sight.ray w i), orb:=seriesC (X:=fun i=>Orders (Book G (big w n i))) (singer H T w) fun w=> ((E).frames w).common
 step_v:= fun i=> T.step_v (slide' w i), top_v:=fun _=> T.top_v w
 step_o:=fun w=> (laterC w).symm
 top_o:=fun z i j hh=> by
    rw [earlierC] at hh; apply T.top_v w; intro he;apply hh; rw [singer,he, Deck.desk_zero] }

variable (hc:Common H)
include hc
lemma knows (hp: H.Follows T) : (grove H w hc).Follows (tele H T w):=by
 intro z; obtain ⟨p,h,hp,hh⟩:= hp w; exact ⟨p,h,hp, rfl⟩
end Vacuum

section Mark
variable {m:ℕ}(T: S.Accounts)(Z:T.Report m)(w:W)

def journey (v:Side):Cover:= v.val • step 0

def shiftE (i:Page (extent M w)): Equiv.Perm (Foot G):= (S.maps (Sight.ray w i)).wind (.across (journey i.bindW))

def beam (p:Page (extent M w)) : Orders (Foot G):= fun i r=> echo (shiftE (S:=S) w p) (Z.main (Sight.ray w p) i r)
-- horizon
variable (HH:H.Follows T)
local notation "A" => tele H T w
local notation "E" => eternal H w
include HH

def gazer : (tele H T w).Report m := {
 main:= beam T Z w
 point:=seriesC (X:=fun p=> Orders (Book G (big w n p))) (fun z e r=>let p:= Page.opening (extent M w) z; (radar H w p).scroll (beam T Z w p e r)) (fun i=> (stations H w i).island m ((tele H T w).orb i.prev))
 step_p :=fun i=>(laterC i).symm
 step_m:=fun i=> by
    let p:=slide' w i; let A₀:=S.frames p
    change A₀.each m (T.bulk p.prev) (beam T Z w i.prev)= fun u v=> echo _ (Z.main p.next u v);rw [← Z.step_m p]; exact step_echo _ (alloy H T HH p) (hort H p) (suitable H p)
 ceilingM :=fun _ a r h=>Z.ceilingM w a r (fun hx=>h (by unfold beam; change echo _ (Z.main (Page.opening M w) _ _)=0;rw [hx,echo_zero]))
 ceilingP :=fun i a r h=>Z.ceilingM w a r (fun hx=>h (by rw [earlierC];dsimp only; unfold beam;change Deck.scroll _ (echo _ (Z.main (Page.opening M w) _ _))= 0;rw [hx,echo_zero,scroll_zero]))
 same:= fun _ _ _=>rfl }
end Mark
end YM.RegulatorIR.Halo
