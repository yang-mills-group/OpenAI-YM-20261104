import YM.Integration.WilsonRootedFusionFirstJoin
import YM.QuadraticLocal.Kiosk

/-! The two original Kiosk certificates retain the same hard arrays for every
comparison. The passive indeterminate follows the actual embedded hard indices
through both mergers, with the measured soft deposits still present. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedKioskReclosure
open Filter Function Finset Lattice Wilson RG Ac Marker
open Push.Corrected Push.AbsoluteSums MeasureTheory RG3 RG3.Ink Ovens Ovens.Pipes
open QuadraticLocal QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached Progress.DirectedRecipe
open WilsonRootedFusionFirstJoin WilsonRootedFusionScratch
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{p:BudgetPoint}{U W Z:Activities G n}
variable {V T ι:Type}[DecidableEq V][Fintype V][Countable ι]{R:Census V}{o:V → Site n}
variable {e f a b m c:ℝ}
variable (H:QuadraticLocal.Hard T p U.forced U.K o R)
variable (D:Kiosk.First p U W e f b)(D₂:Kiosk.Second p W Z f m a c)
variable (M:Canopy.ShiftRows T ι G p o R)

abbrev incumbent (t:T): (layout D.skeleton).Stock p R o:=
  (Kiosk.shape D.oldP D.oldV H).stock D.softens t

abbrev located (t:T): (layout (drawer G n)).Stock p R o:=
  M.stock D₂.softens (Kiosk.shape D₂.oldP D₂.oldV (Kiosk.First.led H D)) t

omit [Fintype V] in
theorem heard (t:T)(i:ℕ)(u:Config G n):
    (located H D D₂ M t).ink (.inl i) u=
      (stuff (Rack.upK D₂.skeleton) (fun k v => Attached.marked D.roll (incumbent H D t) k v) i) u:=rfl

def carried (d:ℕ → Site n → Config G n → Poly R)(h:Site n → ℂ)(t:T)(j:Ovens.Label)(u:Config G n):Polynomial (Poly R):=
  j.elim (fun k => (stuff (Rack.upK D₂.skeleton) (receipt D.roll p (letters (incumbent H D t) d h)) k) u)
    (fun k => Polynomial.C ((located H D D₂ M t).ink (.inr k) u))

omit [Fintype V] in
theorem held (d:ℕ → Site n → Config G n → Poly R)(h:Site n → ℂ)(t:T)(j:Ovens.Label)(u:Config G n):
    (carried H D D₂ M d h t j u).coeff 0=(located H D D₂ M t).ink j u:=by
  cases j with
  | inr k => simp [carried]
  | inl k =>
    rw [heard]
    by_cases here:k∈Set.range (Rack.upK D₂.skeleton)
    · obtain ⟨k,rfl⟩:=here
      simpa only [carried,Sum.elim_inl,stuffed] using (traced D.roll (incumbent H D t) d h k u).1
    · simp only [carried,Sum.elim_inl,blank _ _ here,Pi.zero_apply,Polynomial.coeff_zero]

omit [Fintype V] in
theorem source (d:ℕ → Site n → Config G n → Poly R)(h:Site n → ℂ)(t:T)(i:ℕ)(u:Config G n):
    (carried H D D₂ M d h t (.inl (Rack.upK D₂.skeleton i)) u).coeff 1=
      if (addr D.roll p i).eligible p.threshold u then
        ∑j∈(D.roll i).val,(∏k∈(D.roll i).val.erase j,(incumbent H D t).ink k u)*dye D.skeleton d h j u else 0:=by
  simpa only [carried,Sum.elim_inl,stuffed] using (traced D.roll (incumbent H D t) d h i u).2

def reclosed (d:ℕ → Site n → Config G n → Poly R)(h:Site n → ℂ)(t:T):ℕ → Config G n → Polynomial (Poly R):=
  receipt (folio G n) p (carried H D D₂ M d h t)

omit [Fintype V] in
theorem original (d:ℕ → Site n → Config G n → Poly R)(h:Site n → ℂ)(t:T)(i:ℕ)(u:Config G n):
    let C:=reclosed H D D₂ M d h t i u
    C.coeff 0=(Kiosk.Second.canopy (Kiosk.First.led H D) M D₂).hard t i u ∧
    (C.coeff 0).part R.quiet=(Z.K i u:ℂ) ∧
    C.coeff 1=if (Z.forced i).eligible p.threshold u then
      ∑j∈(folio G n i).val,(∏k∈(folio G n i).val.erase j,(located H D D₂ M t).ink k u)*
        (carried H D D₂ M d h t j u).coeff 1 else 0:=by
  intro C
  have vac:C.coeff 0=(Kiosk.Second.canopy (Kiosk.First.led H D) M D₂).hard t i u:=
    constant (folio G n) (located H D D₂ M t) _ (held H D D₂ M d h t) i u
  refine ⟨vac,by rw [vac];exact (Kiosk.Second.canopy (Kiosk.First.led H D) M D₂).quiet t i u,?_⟩
  rw [D₂.projection]
  dsimp only [C,reclosed,receipt]
  split
  · rw [coefficient]
    simp only [held]
  · simp

theorem attached (i k:ℕ)(head j:Ovens.Label)(q:Site n)
    (left:head∈(folio G n i).val)(seat:Sum.inl (Rack.upK D₂.skeleton k)∈(folio G n i).val)
    (dye:j∈(D.roll k).val)(x:q∈D.skeleton.patch j):
    q∈(Z.forced i).support ∧
    Ac.chain (drawer G n).patch (folio G n i).val head (.inl (Rack.upK D₂.skeleton k)):=by
  have smaller: q∈(addr D.roll p k).support:=(location D.roll p k j j dye dye q x).1
  have shape: D₂.skeleton.kernel k=addr D.roll p k:=by rw [←D₂.oldP,D.projection]
  have enrolled:q∈(drawer G n).patch (.inl (Rack.upK D₂.skeleton k)):=by
    change q∈((drawer G n).kernel (Rack.upK D₂.skeleton k)).support
    rw [Rack.hard_up]
    change q∈(D₂.skeleton.kernel k).support
    rwa [shape]
  rw [D₂.projection]
  exact ⟨(location (folio G n) p i _ _ seat left q enrolled).1,(evidence head)⟩
where
  evidence (head':Ovens.Label)(hx:head'∈(folio G n i).val:=by assumption):
      Ac.chain (drawer G n).patch (folio G n i).val head' (.inl (Rack.upK D₂.skeleton k)):=
    (folio G n i).property.2.1.2 head' hx _ seat
end YM.Integration.WilsonRootedKioskReclosure
