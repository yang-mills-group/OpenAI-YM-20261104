import YM.WilsonCoeffUV.Root.UV.Packed
/-!
# Construct width legs before applying estimates on arbitrary path. Even where only finite jet assigned, entry validity to licence proved (orientation basis as formal equality requires only SOME arbitrary stretch).
Vac reserve Rally: uses one extra order. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V E:Type*}{r h D l j e k a N M m b i:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A B C x y δ σ γ H S O v:ℝ}
-- exact at width not some.
def hemmed (F:Frame G h)(P:Thesis F D)(s:ℝ)(k:ℕ): Prop:=∀ i:Alma F,∀ j≤k,∀ r,∃ A,Twig 0 s A (P i j r)
lemma hemmed.impositionB (F:Frame G h)(P:Thesis F D)(v: Coil F)(p: hemmed F P s k): hemmed F (impose P v) s k:=by
    choose A hA using p; intro i j hj r; simp only [impose,affix,Finset.sum_apply,Pi.smul_apply]; have he u : ∃A,Twig 0 s A (∑ b∈ Finset.antidiagonal j, coeff b.1 (v u i) • P u b.2 r):=by
       let T (b:ℕ ×ℕ):ℝ:= if e:b.2≤k then |coeff b.1 (v u i)| * A u b.2 e r else 0
       refine ⟨_,Cork.sum (M:=T) ?_⟩; intro u hu; have ht:=Finset.mem_antidiagonal.mp hu; dsimp only [T]; rw [dif_pos (show _ from (show u.2≤ k from by omega))]; exact Cork.μ (hA ..) _
    choose a v using he; exact ⟨_, Cork.sum (fun i _=> v i)⟩
lemma rallyFull (H:Hol G)(F:Labels.Frame G h)(p:h<D)(P:Island F D)(hp:Shimmer P)(I:Cloister G h)(R:Stand (inkPin I))(g:Courant I R)(u:hemmed F P.2 I.lamp.input k) (v: ∀ K:ℝ,1≤K →∃ W:Rally (k+1) 0 (inkPin I), W.P=R ∧ W.Q=R ∧ K≤ W.x): hemmed F (legion R P.2) I.lamp.exitS k :=by
    intro i j hj r
    let Y:=P.2 i; have hg:= (streams hp i).born; choose A hA using u; let f (x:ℕ)(w:ℕ):ℝ:= if g:x≤ k then A i x g w else 0; have he (x)(p:x≤k) w:Cork Bank.terrain 0 I.lamp.input (f x w) (Y x w):=by dsimp only [f]; rw [dif_pos p]; exact hA ..
    let Z:=Finset.range (k+1); let l:= valence F i
    let T:= Finset.range (l+k+1)
    let t:=∑ i∈Z,∑ j∈T,f i j; have ht (a)(hp:a∈ Z):0≤ ∑ k∈T,f a k:= Finset.sum_nonneg fun j _=> (he a (Nat.le_of_lt_succ (Finset.mem_range.mp hp)) j).1
    have hZ: 1≤t+1:=by have hw:0≤t:= Finset.sum_nonneg ht; linarith
    obtain ⟨W,g',q',hw⟩:= v _ hZ
    have hh (a b)(p:lowerGrade a b k 0): Shelf Bank.terrain 0 I.lamp.input W.x W.σ (Y a b) (Y a b):= by
       have ha:a∈ Z:= Finset.mem_range.mpr (by unfold lowerGrade at p; omega)
       have hx:= (he a (Nat.le_of_lt_succ (Finset.mem_range.mp ha))); apply Shelf.encore _ W.θ; by_cases h: l+k<b
       · rw [show Y a b=0 from hg a b (by change l+a<b; unfold lowerGrade at p; omega)]; exact Cork.zero.cost (zero_le_one.trans W.rich)
       apply (hx b).cost; have hp: f a b≤ t:=le_trans (Finset.single_le_sum (fun i' _=>(hx i').1) (show b∈T from Finset.mem_range.mpr (by omega))) (Finset.single_le_sum ht ha); linarith
    let U:Tand I.lamp k 0 D:=⟨W,Y,Y,hh⟩
    change ∃ A,Twig 0 _ A (fanfare (inkPin I) R h Y j r); rw [←g']
    by_cases t : lowerGrade j r k 0
    · obtain ⟨v,H⟩:= Fabric.higher (G:=G) t h D; obtain ⟨A,u,p⟩:= H I.lamp; exact ⟨_, (p U).wax⟩
    unfold lowerGrade at t; have ht:j=k:=by omega
    have he':r=0:=by omega
    subst j r
    obtain ⟨q,H⟩:= armada H F k 0 p; obtain ⟨S,u,v⟩:= H I
    obtain ⟨hp,t,hz⟩:= fundsN P P U i rfl rfl hp hp; have hh:Cork Bank.terrain 0 I.lamp.input _ (U.Y k 0):= he k le_rfl 0
    exact ⟨_,(v U (g'.symm ▸ g) (q'.symm ▸ g) (by unfold dues; simp; linarith [I.lamp.inlet]) hp t hz _ 0 hh hh (by change Twig 0 I.lamp.input 0 (Y k 0-Y k 0); rw [sub_self]; exact Cork.zero)).pose⟩

def relight (A: Levels G)(Ñ:ChartRatio G)(n:ℕ)(J:Usage A Ñ n)(I:Cloister G h): Prop:= inkPin I= J.gear ∧∀ N:ℕ,∀ (p:n<N)(g:G.Simple)(u:LocalRatio Ñ)(S:Stand (inkPin I)), HEq S (J.postStand p g u) → Nonempty (Courant I S)
lemma launchW {I T: Gear G}(P:Rally i j I)(q:I=T):∃ W:Rally i j T, HEq W.P P.P ∧ HEq W.Q P.Q ∧ W.x=P.x∧ W.σ=P.σ:= by subst T; exact ⟨P,HEq.rfl,HEq.rfl,rfl,rfl⟩
lemma pickS {I T: Gear G}(P:Stand I)(q:I=T):∃ S:Stand T, HEq S P:= by subst T; exact ⟨P,HEq.rfl⟩
lemma garageC (A:Levels G)(Ñ:ChartRatio G)(u:Usage A Ñ m)(T:Cloister G h)(g:G.Simple)(p:LocalRatio Ñ)(hb:m+1≤ b)(hn:b≤N)(hm:b≤M)(hk:1≤x)(e:rag A m b ≤δ)(v:rag A (m+1) b≤ δ)(hp:u.runs (k+1) 0 δ x N M)(hq:relight A Ñ m u T): ∃ W:Rally (k+1) 0 (inkPin T), HEq W.P (u.postStand (hb.trans hn) g p) ∧ HEq W.Q (u.postStand (hb.trans hm) g p) ∧ W.x=x∧ W.σ=δ:= launchW (u.readPast g p x δ hk hb hn hm e v hp) hq.1.symm
end YM.WilsonCoeffUV.Cosmos
