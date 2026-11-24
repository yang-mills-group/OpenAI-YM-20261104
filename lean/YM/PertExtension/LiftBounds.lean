import YM.PertExtension.MatrixFreeLeaf
import YM.PertExtension.BlendAsymptotic

/-! Bounds on each finite polynomial query, independent of choosing one
infinite stencil type. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.PertExtension.LatticePT
open Function Filter Set Finset MvPolynomial Wilson Lattice Next.Rank Normal Beamer Configuration
open scoped Topology ContDiff Classical BigOperators
variable {q:ℕ+}{G:Gauge}{d n:ℕ}{x:Points n}(hx:x∈conf n)(hq:1<q.val)(U:ℕ→Fin n→Cover)(h:PathReady x q U)
variable {V W Y :Type*}{f:V→Address G}
local notation "reg"=> (Filter.atTop:Filter ℕ)
local notation "C[" g "]" => lifted (q:=q) d U g

def twin {A B:Type*}(σ:A→B)(i:Fin n×(KeyIn G d⊕A)) : Fin n×(KeyIn G d⊕B):= (i.1,Sum.map _root_.id σ i.2)
lemma twin_value (σ:W→V)(a b:Fin n×(KeyIn G d⊕W))(k:ℕ): (C[f] k).cov (twin σ a) (twin σ b)= (C[(f∘σ)] k).cov a b:=by
   have h1 (a:KeyIn G d⊕W): passcode f (magnify q k) d (Sum.map _root_.id σ a)=passcode (f∘σ) (magnify q k) d a:=by cases a <;> rfl
   simp [lifted,primary,twin,h1]
include h hx hq
protected lemma any_lift_bound : PolyFlow.Bounded C[f] reg := by
     intro a b
     let Q:=KeyIn G d
     let W:= {z:V// (Sum.inr z: Q⊕V)=a.2 ∨ (Sum.inr z:Q⊕V)=b.2}
     let σ : W→V:=Subtype.val
     have cf : Finite W :=Finite.of_injective (show ∀ _:W, ↥({a.2,b.2} : Finset _) from fun z:W=>⟨(Sum.inr z.val),by obtain hz|hz:=z.property <;> simp [hz]⟩) (fun x y h'=>Subtype.ext (Sum.inr.inj (congr_arg Subtype.val h')))
     have hu i (hi:i∈({a,b}:Finset _)): ∃ j:Fin n × (Q⊕W),twin σ j=i :=by
        obtain ⟨v,r⟩:=i
        have hz:r=a.2∨r=b.2:= by simp only [Finset.mem_insert,Finset.mem_singleton] at hi;cases hi with | inl h'=>exact Or.inl (congr_arg Prod.snd h') | inr h'=>exact Or.inr (congr_arg Prod.snd h')
        cases r with | inl j=>exact ⟨(v,Sum.inl j),rfl⟩ | inr z=>exact ⟨(v,Sum.inr (⟨z,hz⟩:W)),rfl⟩
     obtain ⟨a',ha⟩:=hu a (by simp);obtain ⟨b',hb⟩:=hu b (by simp)
     have H:=YM.PertExtension.LatticePT.lifted_bounded (q:=q) d hx U hq h (f ∘σ) a' b'
     haveI:Finite W := cf
     obtain ⟨c,hc,ht⟩:=H
     exact ⟨c,ht.mono fun k hv=>(ha ▸ hb ▸ (by rw [twin_value];exact hv))⟩

lemma any_lift_low {f:V→Address G}(s t: Fin n×KeyIn G d): Tendsto (fun k:ℕ => (C[f] k).cov (s.1,.inl s.2) (t.1,.inl t.2)) reg (𝓝 ((currentX hx G d).cov s t)) := by
  by_cases he:s.1=t.1
  · have h1(k): (C[f] k).cov (s.1,.inl s.2) (t.1,.inl t.2)=0:=by unfold lifted primary;  
                                                                     simp [pathSimple,he]
    simp_rw [h1];convert! tendsto_const_nhds using 1; rw [show (currentX hx G d).cov s t=0 from ?_]
    have hu:t=(s.1,t.2):=Prod.ext he.symm rfl; nth_rw 1 [hu]; exact Prayer.dies hx s.1 s.2 t.2
  exact lift_low d hx U hq h f _ _ he _ _

end YM.PertExtension.LatticePT
