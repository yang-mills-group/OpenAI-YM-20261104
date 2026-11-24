import YM.Integration.WilsonMacroscopicRichCommonFiling

/-! Retain the one original signed root ticket at every earlier filing date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichRetainedFilingSale
open MergeProof RG16.Literal Trace.Physical.GermGraph
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
section
open GridApprox
variable (h:Scrim C W u ψ φ δ ζ r D) (L:Stock.Tabs C.path.levels)
variable (J:ℕ) (hV : Stock.Tabs.opens C.path.levels 1 J m) {hk:m≤k}{hN:k<N}
local notation "o"=> fun i=> Mix.camp C p J i
local notation "V"=> Site (C.side J p)
local notation "Bt"=> Stock.census V
local notation "u'"=> hands C p J
local notation "α'"=> march (fun _ : V=> w) φ m k
local notation "h!"=> center C.S p (hV.1.trans (hk.trans hN.le)) 0
variable (f:Config G (C.side N p)→ℂ) (Q:Coefficient (C.labels.level d) (C.side k p)) {c t E:ℝ}
include H h L
local notation "xp"=> C.path.levels.params k
theorem original (ht:C.ref d ≤ m) {hk:m ≤ k} (hN:k<N) (hR:GridApprox.room C.path.levels J k (lensScope C d)) (hC:∀ b:C.label d,Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) (C.O N p b 0))
    (hf :Continuous f)(ha:Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) f) (hr:Q.Format 0 C.params (R k))(hb: Q.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) t) (ht' : (F).coeffSize Q.x+t ≤ c)(hc: 0 < c)(hE:4*(1+(T|>.levels.params k).columns)*c ≤ E)
    (hw: 0 < w)(hP:32*(1+(T|>.levels.params k).columns)*w * ‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2)
    (hZ:Served (R k) (fun i=> radiant (alto T k d) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))) (fun i=>sunny (R k) Q.forced (u' i) (o k i) (alto T k d)) (gust T N p N (birth (Bt) (R N) (fun i=> (center C.S p (hV.1.trans (hk.trans hN.le)) 0).copy i f)) k hN.le) (o k) (α') (C.path.levels.budget k).supportExponent 1) (accounts:credit C N p d f k hN.le=Q.density 0 (C.localSection d) (C.path.rep N p k)) :
    ∃ z:C.label d, Next.UVStress.quota C d k N p z ≤ 2*E ∧
      (center C.S p (hV.1.trans (hk.trans hN.le)) 0).rootTest (C.beta N p) (f-C.O N p z 0) ≤ 2*(stakes C J m/w) ∧
      ∃ (Z:∀ i:ℕ,Coefficient F (C.side i p)) (g:ℕ→ℝ),
        Club C.path C.params Y! (ζ d) ψ m k N p (fun i=>march (fun _:Unit=>2*w) φ m i ()) D Z g hN.le ∧
        (∀ i,m ≤ i → i ≤ k → g i+(F).coeffSize (Z i).x ≤ E/gainChart T k i) ∧
        (Z k).density 0 Y! (R k)=credit C N p d f k hN.le+
          ((s!).entries k (-(s!).terminal.symm z)).density 0 Y! (R k) ∧
        ∀ (i : ℕ), m ≤ i → ∀ (ik : i ≤ k) (door : Opened C d i p),
          mCost C d N p i (topReport C N p d H i door (ik.trans hN.le) f-(s!).terminal.symm z)
            ≤ E / gainChart T k i := by
  obtain ⟨z,cap,root,Z,g,club,prices,close⟩:=root_bequest C N k m p d H w h L J hV f Q ht (hk:=hk)
    hN hR hC hf ha hr hb ht' hc hE hw hP hZ
  rw [← accounts] at close
  exact ⟨z,cap,root,Z,g,club,prices,close,
    WilsonMacroscopicRichCommonFiling.readings (C:=C) (N:=N) (p:=p) (d:=d) (b:=k) (u:=m)
      (X:=Z) (h:=H) (hN:=hN.le) (hh:=club) (f:=f) (hf:=hf) (z:=z) (hR:=close) prices⟩

end
end YM.Integration.WilsonMacroscopicRichRetainedFilingSale
