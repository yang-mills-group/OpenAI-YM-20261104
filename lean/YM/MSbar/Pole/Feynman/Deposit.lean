import YM.MSbar.Pole.Feynman.Process
/-! # Removing `ε`. Value at positive heat scale. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin Symbol Piece
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I]
namespace PoleVal
variable (F : ℂ→Cloud I)
def Ends (H:Cloud I) := ∀ n x,Tendsto (fun z=> F z n x) approaching (nhds (H n x))
def pay : Cloud I := if h:∃ G, Ends F G then Classical.choose h else 0
variable {F}
lemma existsEnd (h: Vortex 0 F): ∃ G, Ends F G:=by
  obtain ⟨R,G,hr,H,h⟩:=h; refine ⟨G 0,fun n x=>?_⟩
  refine Filter.Tendsto.congr' ?_ (((H.budget n).region 0 (zone_zero hr) x).continuousAt.continuousWithinAt)
  exact (neighborhood hr).mono fun z hz=> by simpa only [pow_zero,one_mul] using (h z hz n x).symm
lemma paid {H : Cloud I} (h:Ends F H) : pay F=H:= by
  have hp:=Exists.intro H h; rw [pay,dif_pos hp]; funext n x; apply tendsto_nhds_unique (Classical.choose_spec hp n x) (h n x)
lemma ends (h:Vortex 0 F): Ends F (pay F):= by obtain ⟨G,H⟩:=existsEnd h; rw [paid H]; exact H
lemma harvest {R:ℝ} {G:ℂ→Cloud I} (hr:0<R)(h:Meridian (zone R) G)(he:F =ᶠ[approaching] G) : pay F=G 0:= paid fun n x=> Filter.Tendsto.congr'
      (he.symm.mono fun z hz=> congr_fun (congr_fun hz _) x) (((h.budget n).region _ (zone_zero hr) _).continuousAt.continuousWithinAt)
lemma canonical (h : Vortex 0 F): Canonical (pay F):=by obtain ⟨R,G,hr,H,h⟩:=h; rw [harvest hr H]; exact H.base hr; filter_upwards [neighborhood hr] with z hz; funext n x; simpa using h z hz n x

lemma noShrink {F:ℕ→Cloud I} (k l:ℕ) (hl:k≤l): ∃ C:ℕ → Cloud I,purePolar k F=purePolar l C := by
  let C (i):= if i<k then F i else 0
  refine ⟨C,?_⟩
  induction l, hl using Nat.le_induction with
  | base=> exact ext_cut _ _ C fun i hi=> (if_pos hi).symm
  | succ i hi ih=> rw [purePolar_up,← ih, show C i=0 from if_neg (not_lt.mpr hi)]; simp; rfl
lemma match_counterterm {M S T:Finset I}{a:ℤ}{C G:ℂ→Cloud I}{s:List (Piece I)} (h : Accounts s M a S T C)(p : Accounts s M a S T G): C=G:=by
  have hu:= Vortex.sub (p.endures 1 zero_lt_one) (h.endures 1 zero_lt_one); obtain ⟨i,Q,hj,-⟩:= p.stocks; obtain ⟨k,Z,hq,-⟩:=h.stocks
  obtain ⟨A,hA⟩:=noShrink (F:=Z) k (max i k) (le_max_right ..); obtain ⟨B,hB⟩:=noShrink (F:=Q) i (max i k) (le_max_left ..)
  have hm: G=purePolar _ B:= hj.trans hB; have hn: C=purePolar _ A:=hq.trans hA
  rw [show sum (cooked s M a) M a 1-G-(sum (cooked s M a) M a 1-C) = C-G by abel,hm,hn] at hu
  exact hn.trans ((ext_cut _ _ _ (pole_unique hu)).trans hm.symm)
end PoleVal
namespace Feynman.Menu
variable [Nonempty I] {V:Type}{C : Menu I V} {F:District I V} {μ r:ℝ}

def primitive (C : Menu I V) (μ : ℝ) (F:District I V) (r:ℝ) := Piece.sum (C.run μ F).body C.chart.mom (F.weight C.chart) r

def connected (C:Menu I V) (μ:ℝ) (F:District I V) (s:ℝ) : Cloud I:= PoleVal.pay (C.primitive μ F s)
lemma rolls (hμ:0<μ)(hr:0<r)(h:F.Clear C.chart): Vortex 0 (C.primitive μ F r):= Stack.combined (done C μ h hμ) r hr
lemma approach (hμ:0<μ)(hr:0<r)(h:F.Clear C.chart)(n)(x : External I n) :
    Tendsto (fun z : ℂ=> C.primitive μ F r z n x) approaching (nhds (C.connected μ F r n x)):= PoleVal.ends (rolls hμ hr h) n x
lemma label (hμ:0<μ)(hr:0<r)(h:F.Clear C.chart) : Shape (F.view C.chart) (F.opens C.chart) (C.connected μ F r) := by
  have ht:= senses (fun x hx=>(Stack.graded (done C μ h hμ) x hx).shape) h.notations (F.weight C.chart) r
  exact Shape.transmitted ht (approach hμ hr h)
end Feynman.Menu
end YM.MSbar.Pole
