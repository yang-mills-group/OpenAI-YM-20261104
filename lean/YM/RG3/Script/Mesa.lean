import YM.RG3.Script.Celadon

/-! # Canonical singleton diagnostics on ANY magazine whose
regular/caption part agrees with our issued presentation. Useful after K
merger and/or alignment vs the canonical model. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Edition
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press RG3.Primary RG3.Law Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration Source Push.Local Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n:Side} {V : Type} [DecidableEq V] [Fintype V] {R:Census V}{ζ:V→Site n} {G:Gauge}
  {P : Rep G n} {D:V→ℕ} {H:Hol G} {X:(s:V)→Labels.Frame G (D s)} {L:(s:V)→ SectionData (X s)}
  (d:Deck R P) (σ : Edition ζ R G){z : Deck R P}{k : V→ℝ}

def chapter (s:V) : ℕ:=(numbering (V⊕ℕ)).symm (Sum.inl s)

/-- `z` has the newly arranged canonical regular labels. K and fiscal
references need not agree for this proof. Credentials from PartI's `Readable`
(`foundation_readable` for the standard frame); callers using arbitrary
stencils must also supply one. -/
def editorial (s : V)(hk:Readable H (L s) P.p n (k s))(ho:z.contents.origins=ζ)(he:read P z ζ= σ.sprayed H L d)
    (hz: σ.Principle P.p)(hs:d.Active)(h₁:d.contents.origins=ζ): Canonical s z H (L s):= by
  have he1:=congrArg home he; have he2:=congrArg pins he; have he3:=congrArg song he
  let W:=σ.scribe d
  let c:=chapter s
  have Hc:numbering (V⊕ℕ) c=Sum.inl s:= (numbering _).apply_symm_apply _
  let q:=σ.sprayed H L d
  have hv i : z.contents.support i=q.home i ∧ z.contents.rays i=q.pins i ∧ z.contents.H i=q.song i:=⟨congrFun he1 i,congrFun he2 i,congrFun he3 i⟩
  let d':=Primary.drawer s W H (L s) hk (authorized h₁ hz hs) (dress s W H (L s)).contents rfl rfl rfl rfl W.captions
  have hD (i:ℕ)(hh:i≠c)(hi:z.contents.rays i=R.fire s): z.contents.H i 1=0 ∧
      (Nonwrapping (z.contents.support i) (z.contents.origins s) → H.PiVanish (D s) (z.contents.origins s) (z.contents.H i)):= by
    cases hw:numbering (V⊕ℕ) i with
    | inl x=>
      rw [(hv i).2.1,show q.pins i=R.fire x from revive hw _ _] at hi
      obtain hi:=singleton_inj.mp (congrArg Subtype.val hi : ({x}:Finset V)={s}); subst x
      exact (hh ((numbering _).injective (hw.trans Hc.symm))).elim
    | inr j=>
      obtain ⟨h1,h2,h3⟩:=hv i
      unfold q sprayed at h1 h2 h3; simp only [corsage hw] at h1 h2 h3
      have hg:only (e:=σ) j s:=h2.symm.trans hi
      obtain ⟨hA,hB⟩:= blossom H (L:=L) (d:=d) (σ.shaft_only hg)
      rw [ho,h1,hA,h3,hB]
      exact ⟨d'.no_flat (j+1) (by change j+1 ≠ 0; omega) hg,d'.null (j+1) (by change j+1 ≠ 0; omega) hg⟩
  refine ⟨c,(X s).core (Primary.comp s W H (X s)),?_,?_,?_,?_,fun i h ht=>(hD _ h ht).1,fun i hi h=>(hD i hi h).2⟩
  · exact d'.pure
  · rw [ho,(hv _).1]; exact revive Hc ..
  · rw [(hv _).2.1]; exact revive Hc ..
  rw [ho,(hv _).2.2]; unfold q sprayed; simp only [revive Hc]; rfl

lemma income {w:V→ℝ}{u c v b a κ δ:ℝ}(hw:∀i,0<w i) (s:V)(hk:Readable H (L s) P.p n (k s))(ho:z.contents.origins=ζ)(he:read P z ζ=σ.sprayed H L d)(hz:σ.Principle P.p)(hs:d.Active)(h₁:d.contents.origins=ζ)
    (hb:z.Budget w u c v b a)(hy:z.Active)(hq: P.activities.Valid P.p δ κ){γ:ℝ}(hg:w s*(X s).coeffSize (σ.petition (X:=X) H d s) ≤ γ):
    let Q:= (editorial d σ s hk ho he hz hs h₁).index
    Q.x=Law.legend s z • (X s).e0 + (X s).core (σ.petition (X:=X) H d s) ∧
      w s * ‖Q.x 0‖ ≤ u+a ∧ w s*(X s).coeffSize ((X s).core Q.x) ≤ γ ∧
      Q.Format (z.contents.origins s) H P ∧ Q.remBound (z.contents.origins s) P b (c/(w s)+v/(w s)) ∧ Q.density (z.contents.origins s) (L s) P=fun U=>(z.density U).part (R.fire s):= by
  intro Q
  let h:= editorial d σ s hk ho he hz hs h₁
  have hx (hA:(X s).Coeff) : (X s).core hA (0:(X s).Index)=0:=by simp [Labels.Frame.core]
  have hG:(X s).core (X s).e0=0:=by ext i; by_cases hi:i=0 <;> simp [Labels.Frame.core,hi,Labels.Frame.e0]
  have Hx : Q.x=Law.legend s z • (X s).e0+(X s).core (σ.petition H d s):=rfl
  refine ⟨rfl,?_,?_,h.healthy hy,h.remit hb,candle s z _ _ (h.expose hy hb) hy hb hq⟩
  · rw [Hx,Pi.add_apply,Pi.smul_apply,hx,add_zero,Labels.Frame.e0,Pi.single_eq_same,smul_eq_mul,mul_one]; exact name_income s z hy hb
  rw [Hx,map_add,map_smul,hG,smul_zero,zero_add];
  exact (mul_le_mul_of_nonneg_left ((Work.G08.size_core ..).trans (Work.G08.size_core ..)) (hw s).le).trans hg
end YM.RG3.Script.Edition
