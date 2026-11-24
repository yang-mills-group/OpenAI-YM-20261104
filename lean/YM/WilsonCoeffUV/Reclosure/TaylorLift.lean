import YM.WilsonCoeffUV.Reclosure.PacketWard
/-!
# Reserve for extraction of canonical curvature packets

Wholly on weighted cover symbols. Primitive returns loop BOTH jets (not
only zeroth). Actual frame/symmetry use retains aggregation. Don't
confuse moment budgets with E/K histories on labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary AnalyticNext.QuarticMatch.Estimate Near PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i k r t:ℕ}{s S u v a b:ℝ}

-- Semantic lane
abbrev Stack (G:Gauge)(t:ℕ) := ℕ → Atom G (t+2)
def silentPay (P:Stack G 0) (i:Fin 2→PlaqAxes)(x: Fin 2→G.ColorIndex) (k : ℕ) :=
    if (fun j=> ((P k).leg j).plaq)=i then (P k).coeff x else 0
def forceCoin (P:Stack G 0)(i:Fin 2→PlaqAxes)(x:Fin 2→G.ColorIndex)(k:ℕ)(l:Axis): ℝ:= silentPay P i x k *((((P k).leg 1).offset l- ((P k).leg 0).offset l:ℤ):ℝ)
def Sprite (P:Stack G 0): Prop:= ∀ i x,HasSum (silentPay P i x) 0 ∧∀ l:Axis, HasSum (fun k=>forceCoin P i x k l) 0
private def skeleton (P: Stack G 0) : PathData G:=
   ⟨fun a _=> (0,⟨[],a⟩),P,fun _=>⟨fun _=>(P 0).leg 0,0⟩, fun _=> ⟨fun _=>(P 0).leg 0,0⟩⟩
def awake (P:Stack G t): Prop:= match t with
   | 0=>Sprite P
   | _+1=> True
structure Commission {G:Gauge}{t:ℕ}(P:Stack G t)(σ A:ℝ)(m:ℕ): Prop where
   hue n: (P n).Invariant
   toll : SumBudget (fun n=>(P n).budget σ) A
   loan : 0<m → awake P
variable {P Q:Stack G t}{F:post G (t+1)}
lemma annual (P:Stack G t)(n:Side): written P n 0 (t+2)=rye (seriesScore n P) (t+2) := shine_lit _
lemma fiscal (F: Stack G t)(i s): 0≤ (F i).budget s:=by unfold Atom.budget Atom.magnitude; positivity
lemma Commission.change (w:Commission P s a k)(t:S ≤ s)(e:a≤b): Commission P S b k:= ⟨w.hue,let h:= budget_minor w.toll (fun n=>fiscal P n S) (fun n=>mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right t (by positivity))) (Finset.sum_nonneg (fun _ _=> abs_nonneg _)));
    ⟨h.1,h.2.1,h.2.2.trans e⟩,w.loan⟩
lemma roadHue (h:Blue.Smooth F)(u:stroll F)(w:∀ x c,windsL x c F=0)(v:Bank.mural F)(hp:Amber terrain s a F)(he:0<s): Features (pictures F) (hingeZ s (t+1)) (a*hinges s (t+1)):= hues hp he h u w v
lemma sized (P:Stack G t) (h:0<s)(hw:Commission P s a m)(F:post G (t+1))(e: Amber terrain u b F)(ht:0<u)(hp:stroll F)(hv:∀ n:Side,rye (seriesScore n P) (t+2)=lagoon F n): fire P 0 (t+2)=F:= Yields.unique (paid_packet h hw.toll (by omega) 0 (t+2)) ((lagoon_yields e ht hp).congr (Eventually.of_forall fun n=> ((annual P n).trans (hv n)).symm))
/-- All ordinals pinned to actual paths (route about canonical anchor, with
face signs read in a separate rotation channel). No independent retuning of
length per cutoff inside a display. -/
def deeds (G:Gauge) (t:ℕ) : ℕ → Fin (t+2) → RG.Slot := fun i=> (issue (0:Skin G (t+1)) i).leg
def Deed (P: Stack G t):Prop:= ∀ i,(P i).leg=deeds G t i
lemma scripted (X:Skin G (t+1)): Deed (t:=t) (issue X):= fun _=>rfl
-- rank-two extraction anticipations

def First (G:Gauge)(s:ℝ)(m r:ℕ)(S K:ℝ) := ∀ (A:ℝ)(F : post G (r+1)), Amber terrain s A F → stroll F → Bank.mural F → Blue.Smooth F → (∀ x c,windsL x c F=0) → (∀ h:r=0, Spin (h ▸ F) ∧ (0<m→ Aware (h ▸ F))) →∃ P:Stack G r, Commission P S (K*A) m ∧ Deed P ∧ (∀ n:Side,rye (seriesScore n P) (r+2) = lagoon F n) ∧ fire P 0 (r+2)=F
lemma painted_two (G:Gauge)(s:ℝ)(he:0<s) (m:ℕ):∃ v C,0<v ∧ v≤ s ∧ 0≤ C ∧ First G s m 0 v C:=by
   let a:=hingeZ s 1
   let b:=hinges s 1
   have hh:0<a:= hinge_paid he 1; have hB:0≤b:= (hinge_reserve he 1).le
   obtain ⟨μ,K,hM,hμ,hk,H⟩:= veins G a hh
   have hx:0 ≤ inkCost G 1 μ:=inkCost_nonneg ..
   let V:=K*b*inkCost G 1 μ
   have HT: μ≤ s:= hμ.trans (by unfold a hingeZ; push_cast; linarith)
   refine ⟨μ,V,hM,HT,mul_nonneg (mul_nonneg hk hB) hx,?_⟩
   intro A F u p w f t g
   let D:= pictures F; let n:= if m=0 then 0 else 2
   have hb:= roadHue f p t w u he
   have he x y: Rays (n+2) (D x y ∘ axes):=by unfold n; split; · exact infer₂ u (by assumption) f _ _ t (g rfl).1
                                              next he' => exact infer₃ u he f _ _ ((g rfl).2 (by omega)) (g rfl).1
   obtain ⟨X,T,hw⟩:= H _ n _ (mul_nonneg u.1 hB) hb he
   let Z:Stack G 0:= issue X
   have hv : Commission Z μ (V*A) m:=by
      have h:= artery_funded T
      refine ⟨h.2, by unfold V; convert! h.1 using 1; unfold b; ring,?_⟩
      intro hm
      apply (show Sprite Z from ?_)
      have H : n = 2:= by unfold n; rw [if_neg]; omega
      rw [H] at hw
      exact issue_normal T.price hM hw (skeleton Z) rfl
   have hx m:= proof_marks (F:=F) hM u (by assumption) f p T m
   exact ⟨Z,hv,scripted X,hx,sized _ hM hv F u (by assumption) p hx⟩
lemma novae (G:Gauge)(s:ℝ)(he:0<s)(m t:ℕ) : ∃v C,0<v ∧ v≤s ∧ 0≤ C ∧ First G s m t v C := by
   cases t with
   | zero=> exact painted_two G s he m
   | succ t=>
     let a:=hingeZ s (t+2); let b:= hinges s (t+2)
     have hh:0<a:= hinge_paid he _; have hB:0≤ b:=(hinge_reserve he _).le
     obtain ⟨μ,K,hM,hμ,hk,H⟩:= strokes G (t+2) (by omega) a hh
     let V:= K*b*inkCost G (t+2) μ; have hV:0≤ V:= mul_nonneg (mul_nonneg hk hB) (inkCost_nonneg ..)
     have he' :μ≤s:= hμ.trans (by unfold a hingeZ; apply div_le_self he.le; exact_mod_cast show 1 ≤ 2*((t+2)+1) from by omega)
     refine ⟨μ,V,hM,he',hV,?_⟩; intro A F u p w f e _
     obtain ⟨X,T⟩:= H _ _ (mul_nonneg u.1 hB) (roadHue f p e w u he)
     let Z:Stack G (t+1):= issue X
     have hv : Commission Z μ (V*A) m:=by
        have h:= artery_funded T; refine ⟨h.2, ?_, fun _=> trivial⟩; unfold V; convert! h.1 using 1; unfold b; ring
     have hx m:= proof_marks (F:=F) hM u he f p T m
     exact ⟨Z,hv,scripted X,hx,sized _ hM hv F u he p hx⟩
-- Move route registry after paying enlarged lengths, Taylor NOT equal except leading. top-wise history budgets survive reclosure.
structure Reroute (P Q:Stack G t): Prop where
   paint i: (P i).coeff=(Q i).coeff
   target i j:((P i).leg j).plaq=((Q i).leg j).plaq
   ends i j: ((P i).leg j).offset=((Q i).leg j).offset
lemma toll_reroute (h:Reroute P Q)(e:∀ i, S*(Q i).length≤ s*(P i).length+u)(p: SumBudget (fun i=>(P i).budget s) a): SumBudget (fun i=>(Q i).budget S) (Real.exp u *a):= by
   apply budget_minor (cap_scale p (Real.exp_pos u).le) (fun i=> fiscal Q i S); intro i
   unfold Atom.budget Atom.magnitude; rw [h.paint i,mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun _ _=>abs_nonneg _); rw [← Real.exp_add,add_comm u]; exact Real.exp_le_exp.mpr (e i)
lemma rerouted (h:Reroute P Q)(p: Commission P s a m)(e:∀ i, S*(Q i).length≤ s*(P i).length+u): Commission Q S (Real.exp u*a) m:=by
   refine ⟨fun i=>?_,toll_reroute h e p.toll,?_⟩
   · have he : (Q i).poly=(P i).poly:= by funext v; simp only [Atom.poly,h.paint i]
     intro w a; simp_rw [he]; exact p.hue ..
   intro x; have hw:=p.loan x; cases t with
   | succ i=> trivial
   | zero=>
      have he i x:silentPay Q i x = silentPay P i x:=by funext j; unfold silentPay; simp_rw [h.target,h.paint]
      change Sprite Q; change Sprite P at hw; intro i x
      refine ⟨he i x ▸ (hw i x).1,fun j=>?_⟩
      have H: (fun k=>forceCoin Q i x k j)=fun k=>forceCoin P i x k j:= by funext k; unfold forceCoin; rw [h.ends,h.ends,he]
      rw [H]; exact (hw i x).2 j
lemma path_dance (h:Reroute P Q)(p: Commission P s a m)(q:Commission Q S b m)(hS:0<s)(ht:0<S)(n:Side): rye (seriesScore n Q) (t+2)=rye (seriesScore n P) (t+2):=by
   have hh:volumeInk n P=volumeInk n Q:= by
      ext1 v; rw [ink_apply n P hS p.toll,ink_apply n Q ht q.toll]; apply Finset.sum_congr rfl; intro i _; apply tsum_congr; intro x
      rw [ink_note,ink_note,h.paint]; apply Finset.sum_congr rfl; intro j _; simp only [Work.F03.slotFace,h.ends,h.target]
   funext x; rw [fiscal_vol,fiscal_vol,total_ink n Q ht q.toll,total_ink n P hS p.toll,hh]
end YM.WilsonCoeffUV.Bank.Mosaic
