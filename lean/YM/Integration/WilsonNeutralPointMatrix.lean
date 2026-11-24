import YM.FormalBulk08.Roof.Attic
import YM.FormalBulk08.Sierra.Camping

/-! The native free leading matrix at an individual fine child.  The same
held-field Wick push, running coupling, shifted test and original detector are
kept before the sum over fine positions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralPointMatrix
open FormalBulk08
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Sierra
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical

variable {G:Gauge}{d j t D l u:ℕ}{K:KernelChoices}{o:Loc G 1}

def child (P:Flight j t)(V:Lodge P.patch)(W:Pot G)(a:hue G)(ρ:ChartRatio G)
    (h:P.patch.Branches K G)(hL:2≤P.L.val)(d u:ℕ)(x:Site P.L)(Y:Anthem D G):
    Anthem D G:=fun f=>(P.L.val:ℝ)^d • enterStep P V W a ρ h u (stepsong P Y hL f x)

theorem highest (Y:Anthem D G)(hy:Wade o Y l)(P:Flight j t)(V:Lodge P.patch)
    (ρ:ChartRatio G)(h:P.patch.Branches K G)(hL:2≤P.L.val)(W:Pot G)
    (hw:Vivid W)(hr:LocalRatio ρ)(f:Studio D)(u:ℕ)(x:Site P.L):
    braise P V W (stepsong P Y hL f x) ρ h u 0 l =
      lowmost P K V x (Y (throughW x D hL f) 0 l):=by
  let Z:=stepsong P Y hL f x
  let T:=border P V W Z ρ h
  unfold braise
  rw [Finset.sum_eq_single 0]
  · rw [border,dipper_first];rfl
  · intro v _ hv
    have he:T v 0 l=0:=by
      by_contra live
      have hz:=step_can o P Y hy hL f x
      have ht:=(youth_egg _ (convict P V Z (K:=K) hz) (fairy W ρ P V K hw hr) v 0 l live).2
      omega
    change jetty _ (T v 0 l)=_;rw [he];rfl
  · simp

private theorem young (o:Loc G 1)(P:Flight j t)(V:Lodge P.patch)(W:Pot G)(a:hue G)(ρ:ChartRatio G)
    (h:P.patch.Branches K G)(hL:2≤P.L.val)(d u:ℕ)(x:Site P.L)(Y:Anthem D G)(f:Studio D)
    (hy:Wade o Y l)(hw:Vivid W)(hr:LocalRatio ρ):
    Young (child P V W a ρ h hL d u x Y f) l:=by
  let A:=braise P V W (stepsong P Y hL f x) ρ h u
  have success:Young A l:=truss P V W _ ρ h hw hr (step_can o P Y hy hL f x) u
  intro e r nonzero
  by_contra contradiction
  apply nonzero
  change (P.L.val:ℝ)^d • (∑ b∈Finset.range (e+1),bill _ _ e b r • A b r)=0
  rw [Finset.sum_eq_zero,smul_zero];intro b hb
  have old:A b r=0:=by
    by_contra live;have gain:=success b r live
    unfold Yield at gain contradiction;rw [Finset.mem_range] at hb;omega
  rw [old,smul_zero]

theorem diagonal (F:Frame G d)(Y:Anthem D G)(i:Letter F)(hy:Clef o Y (slots F i))
    (q:ℕ)(lower:∀ j:Letter F,Pose.weight F j<q→slots F j=slots F i→coeff 0 (echo F Y j)=0)
    (P:Flight j t)(V:Lodge P.patch)(ρ:ChartRatio G)(a:hue G)(h:P.patch.Branches K G)
    (hL:2≤P.L.val)(W:Pot G)(H:Hol G)(hp:d<D)(hd:d≤j)(ht:4≤t)(hq:q≤d)
    (w:Vivid W)(hr:LocalRatio ρ)(hi:Pose.weight F i≤q)(u:ℕ)(x:Site P.L):
    coeff 0 (echo F (child P V W a ρ h hL d u x Y) i)=
      heightK P.L d (Pose.weight F i)*coeff 0 (echo F Y i):=by
  let n:=slots F i
  let p:=inside F i D
  let f:=throughW x D hL p
  obtain ⟨σ,A,hs,_,T⟩:=hy.fare.2.2 0 n
  obtain ⟨η,B,hη,hb,hB⟩:=aone P (K:=K) G ht
  let z:=min η (P.L.val*σ)
  have hz:0<z:=lt_min hη (mul_pos (by positivity) hs)
  have horizon:=strip_mono hB (min_le_left (b:=P.L.val*σ) η) le_rfl
  have gain:=pearl_credit F Y hy σ hs q n lower
  obtain ⟨C,_,Hx⟩:=Lodge.bothPay G K V z hz
  have hx:=Hx _ _ hb horizon
  have high:=uranic o P V x hz (min_le_right (a:=η) _) hs.le (T f) (hy.fare.2.1 f 0 n)
    (gain.2.1 f) horizon hb hx.1 hx.2.1
  simp only [zero_mul,mul_zero] at high
  have transfer:=sub_eq_zero.mp (lease_cut o _ high)
  have finite:=upheave (o:=o) _ x (grown_budget G _ hb horizon) hb
    (min_le_right (a:=η) _) hz.le (T f)
  change Knoxville _ _ _ (upmost P.L x (chair P G K) (Y f 0 n)) _ at finite
  rw [echo_nil,echo_nil]
  change pearlJ F ((P.L.val:ℝ)^d • stamp _ _ _ 0 n) (mint F i)=_
  rw [Wine.paid_nil _ _ _ n (book_fresh _) (book_guard _),highest Y hy.fare P V ρ h hL W w hr p u x,transfer,
    chalk_amp F _ finite hz,traction o F Y hy q hp hq i rfl hi P hd ht H K hs gain x hL
      (fun p=>⟨_,T p⟩) hz (min_le_right ..) horizon hb]
  unfold heightK Dawn.scale unitStep
  ring

theorem filed (o:Loc G 1)(F:Frame G d)(Y:Plaza F D)(ρ:ChartRatio G)(a:hue G)
    (P:Flight j t)(V:Lodge P.patch)(h:P.patch.Branches K G)(hL:2≤P.L.val)(W:Pot G)
    (H:Hol G)(hp:d<D)(hd:d≤j)(ht:4≤t)(hv:Story W (pink K.penalty P.wing))
    (hr:LocalRatio ρ)(hy:Court o F Y)(x:Site P.L):
    Colfax (slots F) (Pose.weight F) (pantry F (child P V W a ρ h hL d d x ∘ Y))
      (fun i=>heightK P.L d (Pose.weight F i)):=by
  refine ⟨?_,fun _=>height_install ..,?_⟩
  · intro i j e more
    let T:= child P V W a ρ h hL d d x (Y j)
    change coeff e (echo F T i)=_
    rw [echoline];apply Finset.sum_eq_zero;intro r hrange;split
    · rename_i gap
      rw [show T (inside F i D) _ r=0 from ?_,chalk_void]
      by_contra live
      have rank:=young o P V W a ρ h hL d d x (Y j) (inside F i D)
        (hy.officers j).fare hv.toVivid hr _ _ live
      unfold Yield at rank;rw [Finset.mem_range] at hrange;omega
    · rfl
  · intro i j same lower
    have held:Clef o (Y j) (slots F i):=same.symm ▸ hy.officers j
    have gain:=diagonal F (Y j) i held (Pose.weight F j) (fun z hz _=>by
      rw [hy.city z j,if_neg (show z≠j from fun eq=>by subst z;exact (lt_irrefl _ hz)),map_zero])
      P V ρ a h hL W H hp hd ht (weightFits F j) hv.toVivid hr lower d x
    change coeff 0 (echo F (child P V W a ρ h hL d d x (Y j)) i)=_
    rw [gain,hy.city];by_cases eq:i=j <;>simp [eq]

end YM.Integration.WilsonNeutralPointMatrix
end
