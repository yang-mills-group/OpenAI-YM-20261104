import YM.MSbar.Pole.Sew.List
/-! # Lifting a pipe by any incidence computation -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Piece
open Set Function Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I]

/-- Interior seam. -/
def leap (T:Thread I)(μ:ℝ) (p : Piece I) : Piece I := ⟨p.l+1, Integrates μ (T.spun 1 p.g)⟩
/-- No loop. -/
def ramp (T:Thread I)(L:Finset I)(p:Piece I): Piece I:= ⟨p.l,T.twig L 1 p.g⟩

variable {A : Finset I} {Y : Finset I} {s : List (Piece I)} {T : Thread I}
variable (hT:T.Fits Y) {b:ℤ} (ha:T.inputs ⊆ A) (hr:Disjoint A (T.chain.reads∪Y))
include hT ha hr
local notation "κ" => (T.inputs∪(T.chain.reads∪Y))
local notation "τ" => (T.chain.reads∪Y)
lemma self_flow (h: ∀ x∈s,Single x A b κ τ) {t:ℝ}(ht:0<t)(μ : ℝ) :
    Integrates μ (T.spun t (sum s A b t)) =ᶠ[approaching] sum (s.map (leap T μ)) A (b-2-T.chain.demand) t:= by
  induction s with
  | nil=> rw [sum_nil,T.integrates_zero]; rfl
  | cons i s ih=>
    obtain h' : ∀ x∈s, Single x A b κ τ := fun x hx=>h x (List.mem_cons_of_mem _ hx)
    obtain ⟨⟨k,hK⟩,hp,hL⟩:= h i List.mem_cons_self
    have hh: Acts κ τ (roll A ⟨b,i.l⟩ t i.g):= Filter.Eventually.mono (p:=fun z=>Shape _ _ _) hp fun z hz => (hz.move_by A hr t).scale _
    obtain ⟨m,hm⟩:= rough (fun x hx=>(h' x hx).swirl) A b t ht
    have hv := additive hT (roll_vortex A ⟨b,i.l⟩ hK ht) hm ht hh (senses (fun x hx=>(h' x hx).shape) hr b t) μ
    change Integrates μ (T.spun t (roll A {a:=b,l:=i.l} t i.g+sum s A b t)) =ᶠ[approaching] sum (_ :: _) _ _ _
    rw [sum_cons]; exact hv.trans ((arrives A hT ha hr ⟨b,i.l⟩ ht hK hp μ).add (ih h'))
lemma supply (h : Stack s A b κ τ) (μ:ℝ) (hμ:0<μ): Flag (s.map (leap T μ)) A (b-2-T.chain.demand) (T.layout Y) Y:= by
  constructor
  · intro x hx; obtain ⟨q,hq,rfl⟩:= List.mem_map.1 hx
    obtain ⟨⟨k,hk⟩,hj,H⟩:=h.graded q hq; have he:= fused hT 1 zero_lt_one hk hj μ hμ
    exact ⟨⟨k,he.1⟩,he.2, fun hy=>by simp [leap] at hy⟩
  intro r hv
  exact Piece.congr (fused hT r hv (h.combined r hv) (senses (fun x hx=>(h.graded x hx).shape) hr b r) μ hμ).1 (self_flow hT ha hr h.graded hv μ)

lemma bridge (h: ∀ x∈s,Single x A b κ τ) {t:ℝ}(ht:0<t) (L : Finset I)(hp:L⊆T.output) :
    T.twig L t (sum s A b t) =ᶠ[approaching] sum (s.map (ramp T L)) A (b+2-T.chain.demand) t := by
  induction s with
  | nil=> unfold twig load; rw [sum_nil,spun_zero]; rfl
  | cons i s ih=>
    obtain hl:=h i List.mem_cons_self
    filter_upwards [hl.shape,ih (fun x hx=>h x (List.mem_cons_of_mem _ hx))] with z hz hv
    change T.twig _ _ _ z= (sum (_::_) _ _ _) z; rw [sum_cons, sum_cons]
    funext n x
    unfold twig
    rw [spun_add]
    calc
      _ = T.twig L t (roll A {a:=b,l:=i.l} t i.g) z n x+ T.twig L t (sum s A b t) z n x:= rfl
      _ = _:= by rw [bridge_scale A hT ha (Finset.disjoint_left.mpr (fun i hi h=>Finset.disjoint_left.mp hr hi (Finset.mem_union_left _ h))) _ ht _ hp
                           (fun i hi=> hz.angle i (Finset.mem_union_left _ hi)),hv]; rfl
lemma piers (h : Stack s A b κ τ) (L : Finset I)(hp:L⊆T.output): Flag (s.map (ramp T L)) A (b+2-T.chain.demand) (T.layout Y) Y := by
  constructor
  · intro x hx; obtain ⟨i,hi,rfl⟩:= List.mem_map.mp hx
    obtain ⟨⟨k,hk⟩,hj,ht⟩:=h.graded i hi; obtain ⟨hm,hH⟩:=offered hT 1 zero_lt_one hk hj hp
    refine ⟨⟨k,hm⟩,hH,fun he=>?_⟩
    change i.l=0 at he
    have hx:= at_zero A L hT b ha (Finset.disjoint_left.mpr (fun i hi h=>Finset.disjoint_left.mp hr hi (Finset.mem_union_left _ h))) hp (ht he) hj rfl
    change ∀ᶠ z in _,∀ n x, Tendsto (fun s=> roll A ⟨b+2-T.chain.demand,i.l⟩ s (T.twig L 1 i.g) z n x) _ (nhds 0); rw [he]; exact hx
  intro r hv
  exact Piece.congr (offered hT r hv (h.combined r hv) (senses (fun x hx=>(h.graded x hx).shape) hr b r) hp).1 (bridge hT ha hr h.graded hv L hp)
end YM.MSbar.Pole.Piece
