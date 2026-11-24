import YM.OPE.Compatible.Ivy.Glee
/-!
# Bounds costs uniform with common weights w.cap. handshake per μ, which transport converse not assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Char
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
variable {I J E:Type} [Fintype I] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]{μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E}
variable {k m d e n:ℕ}{p:Phase}{s:Meeting}{Ω:Row I I}{S:Story I}{P:Curtain I}{t:Side}{x:deck I t}{j:Site t}{Z:E→L[ℝ] deck I t}
def Strut (p i:Phase):= Finset.univ.filter (fun t:Phase=> t.val+i.val=p.val)
def shout (p i j:Phase):= Finset.univ.filter (fun t:Phase=>t.val+i.val+j.val=p.val)
omit [Fintype I] in lemma π_bd (w:ℝ)(b:Meeting)(hb:1≤w): Visit (fun (_:Ask)=>w) b ≤ w^5:=by unfold Visit;rw [prod_const]; exact pow_le_pow_right₀ hb (b.card_le_univ.trans_eq (Fintype.card_fin _))
omit [Fintype I] in lemma scaledV (b:ℝ)(P:Curtain I)(k:ℕ): Flair (b • P) k x j=b* Flair P k x j:=flairCost ..
def stretchH (Ω:Row I I)(S:Story I)(P:Curtain I)(d:ℕ)(i j:Phase): Curtain I:= ∑ k∈ Plans j, (meter k) • rootCush S Ω k (d+i.val) P
def Mouth (Ω:Row I I)(S:Story I)(X:Spring I)(d:ℕ) (p:Phase) :=∑ i:Phase,∑ k∈Strut p i, stretchH Ω S (X i) d i k
lemma whorl (x:ℕ)(k:Meeting): x+HueS k≤x+44:=by unfold HueS;have he:k.card≤5:= k.card_le_univ.trans_eq (Fintype.card_fin _);omega
lemma move_up (p i j:Phase)(h:j∈ Strut p i) (d:ℕ): d+i.val+j.val=d+p.val:=by have hp:=Finset.mem_filter.mp h|>.2;omega
abbrev glideZ (d:ℕ):= d+2+40
lemma glideB (p i j:Phase)(d:ℕ)(h:j∈ Strut p i): extendK (d+i.val) j ≤ glideZ d:=by unfold extendK glideZ; rw [move_up p i j h d]; have hp:=p.isLt;change p.val<3 at hp;omega
lemma mountK (p i j:Phase)(h:j∈Strut p i)(d n k:ℕ)(s K:ℝ)(C:ℕ→ℝ)(hs:0<s)(hK:0≤K)(hC:0≤C)(hp:n+44≤k):∃ A:ℝ,0≤ A ∧∀ (t:Side)(E: Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)(Ω:Row I I), Ω.strip s K →∀ (S:Story I)(c:ℝ)(x:deck I t)(Z:E→L[ℝ] deck I t)(a:Site t), Ribbon S Ω Z L x a k C c→forall w:ℝ,1≤w→weightsB S k (fun _=> w)→∀ (X:Curtain I)(b:ℝ),Volume X (d+i.val) k b→ let V:=stretchH Ω S X d i j; Volume V (d+p.val) k (A*w^5*b)∧ Mold ((rich (Tap μ L (Char.Sketch S c x Z) (Char.Ωx (d+i.val) X Z x a))).seq j.val) (Flair V (d+p.val) x a) (A*w^5*b*(1+‖x‖)^glideZ d) t n:=by
     classical
     let v:= Plans j; choose! F hf H using (fun b h=> pano (I:=I) j b h s K C hs hK hC (d+i.val) k n ((whorl n b).trans hp)); let c (i):= ‖meter i‖*F i; refine ⟨∑ i∈v,c i, sum_nonneg (fun i hi=>mul_nonneg (norm_nonneg _) (hf _ hi)),?_⟩; intro t E _ _ _ _ _ μ _ L Ω hΩ S y x Z a hS w hw hW X b hB V; let K(b):= Char.Sketch S b x Z; let T:= Tap μ L (K y) (Char.Ωx (d+i.val) X Z x a); let p':=d+p.val; let P(i':Meeting):= rootCush S Ω i' (d+i.val) X; let T'(u:Meeting):=meter u • P u
     have hb:= Sack.coins (hB.2 0); let r(k:Meeting):= Visit (fun _=> w) k; have hr(i')(hi:i'∈v): Volume (P i') p' k (F i' * b*r i') ∧ Mold (T i') (Flair (P i') p' x a) (F i' * b*r i'*(1+‖x‖)^extendK (d+i.val) j) t n:= by
          have hv := H i' hi _ _ μ L Ω hΩ S y x Z a hS _ hW X b hB; obtain ⟨ht,hp⟩:= hv; rw [move_up p i j h d] at ht hp; exact ⟨ht,hp⟩
     have hW(i')(hi:i'∈v): F i'*b*r i' ≤ F i'*w^5*b:= (mul_le_mul_of_nonneg_left (π_bd w _ hw) (mul_nonneg (hf _ hi) hb)).trans_eq (by ring)
     have hh(i')(hi:i'∈v):Volume (T' i') p' k (c i'*w^5*b):= ((hr _ hi).1.spread _ _).raise _ le_rfl ((mul_le_mul_of_nonneg_left (hW _ hi) (norm_nonneg _)).trans_eq (by unfold c;ring)); let z:=(1+‖x‖)^glideZ d
     have hx(i')(hi:i'∈v): Mold (meter i'*T i') (Flair (T' i') p' x a) (c i'*w^5*b*z) t n:=by
          rw [show Flair (T' i') p' x a= _ from scaledV (meter i') (P i') p']; apply (sculpt (hr _ hi).2 (meter i')).trans; refine (mul_le_mul_of_nonneg_left (mul_le_mul (hW _ hi) (pow_le_pow_right₀ (by simp) (glideB p i j d h)) (by positivity) (by have ht:= hf i' hi; positivity)) (norm_nonneg _)).trans_eq ?_; unfold z c;ring
     constructor
     · rw [Finset.sum_mul,Finset.sum_mul]; exact Volume.sum T' _ v hh
     rw [role,show V= ∑ i∈v,T' i from rfl, flairS (d+p.val) x a T' (fun i hi=> Volume.bound _ (hh _ hi))]; refine (moldSum hx).trans_eq ?_; rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
end YM.OPE.Libra.Char
