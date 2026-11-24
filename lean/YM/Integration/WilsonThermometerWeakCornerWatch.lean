import YM.Integration.WilsonThermometerWeakCornerJets
import YM.Integration.WilsonThermometerWeakWatchedFaces

/-! The ordinary continuum reading of each named Wilson face on the same
registered exterior as the source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCornerWatch
open Function Filter Finset Set MeasureTheory Spec Table Extraction Trace Trace.Pilot OPE
open Next.UVStress GapsContact Frontier6 Frontier6.Tale PhysicalNext.Repeat.Legato Wilson RG
open WilsonThermometerWeakCornerJets WilsonCenteredWatchedShape
open WilsonPositionThermometerCapStation WilsonThermometerWeakWatchedFaces
open scoped Classical Topology

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S){n:ℕ}

def near (d:Fin n→ℕ)(u:∀i,R.family.label (d i))(i:Fin n):S.Tag:=
  S.classTokens ⟨d i,u i⟩

def outside (W:Watch R.family): Fin W.n → S.Tag:= S.classTokens ∘ W.q

theorem named (q:StateIndex F)(d:Fin n→ℕ)(u:∀i,R.family.label (d i))
    (W:Watch R.family)(ρ:ℝ)(x:Points n)
    (clear:Injective (sites ρ x (fun j:Fin W.n=>W.held j.succ))):
    panel F q (near (S:=S) R d u) (outside (S:=S) R W) (fun j:Fin W.n=>W.held j.succ) ρ x =
      (state F q).read (joint W ρ x) (WilsonCenteredWatchedCylinder.tags R d u W):=by
  let e:Fin (n+W.n) ≃ Fin n ⊕ Fin W.n:= finSumFinEquiv.symm
  have pos:WithLp.ofLp (joint W ρ x) = sites ρ x (fun j:Fin W.n=>W.held j.succ) ∘ e:=by
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simp [joint,sites,e]
    · simp [joint,sites,e]
  have actual: joint W ρ x∈conf (n+W.n):=by
    change Injective (WithLp.ofLp _)
    rw [pos]
    exact clear.comp e.injective
  have arms:Sum.elim (near (S:=S) R d u) (outside (S:=S) R W) ∘ e =
      S.classTokens ∘ WilsonCenteredWatchedCylinder.tags R d u W:=by
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simp [WilsonCenteredWatchedCylinder.tags,near,e]
    · simp [WilsonCenteredWatchedCylinder.tags,outside,e]
  have ex:=Tale.remap S (state F q) (sites ρ x (fun j:Fin W.n=>W.held j.succ))
    (Sum.elim (near (S:=S) R d u) (outside (S:=S) R W)) e (joint W ρ x) pos
    (hierarchy F q).laws.toSymmetric
  rw [if_pos clear,arms,S.at_project _ (hierarchy F q).laws.toSymmetric (respects F q) actual] at ex
  unfold panel
  rw [←Tale.concatenates]
  exact ex

theorem face {cap:ℕ}(d:Fin n→Fin (cap+1))(Z:Group R.family cap)
    (v:∀i,(Climb.Bel R.family.book).Field (d i))(W:Watch R.family)(ρ:ℝ)
    (s:Finset (Fin n)){x:Points n}(clear:Injective (sites ρ x (fun j:Fin W.n=>W.held j.succ))):
    heard (S:=S) R d Z v W ρ s =ᶠ[𝓝 x]
    panel F none (near (S:=S) R (fun i=>(d i).val) (mask R d s (fun i=>Z.lift (index Z (d i)) (Z.change (d i) (v i)))))
      (outside (S:=S) R W) (fun j:Fin W.n=>W.held j.succ) ρ :=by
  have ready:∀ᶠ z in 𝓝 x,Injective (sites ρ z (fun j:Fin W.n=>W.held j.succ)):=by
    apply Tale.larger (X:=Points n) _ clear
    apply continuousAt_pi.mpr
    intro i
    cases i with
    | inl i=>exact (PiLp.continuous_apply 2 _ i).continuousAt.const_smul ρ
    | inr i=>exact continuousAt_const
  filter_upwards [ready] with z hz
  exact (named R F none _ _ W ρ z hz).symm

end YM.Integration.WilsonThermometerWeakCornerWatch
end
