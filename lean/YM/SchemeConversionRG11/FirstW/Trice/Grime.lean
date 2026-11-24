import YM.SchemeConversionRG11.FirstW.Trice.ClayMap
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{G:Gauge}{p:Nodes}{n:Side}{r:ℕ}
abbrev Rule (p:Points 3)(a b c:Trio G):= amount p (![a,b,c])
lemma stamped_rule (p:Points 3) : ∃ L:StampC G,∀ a b c,L a b c=Rule p a b c:= stamps (tallG p)
lemma codeP (b:Badge G)(p:P)(e:Bool): copyK G p (Glyph b e)= dynasty ⟨b,p,e⟩ := glyphS ⟨b,p,e⟩
abbrev β (b:Badge G) := Glyph b true
abbrev θ (b:Badge G) := Glyph b false
def pact (p:Nodes)(a b:Badge G)(k:P):ℂ:=if a.2=b.2 then mixed a.1 b.1 (p 0-p k) else 0
lemma pact_eq (hp:p∈conf 3)(a b:Badge G){k:P}(hk:k≠0): lux p ⟨a,0,true⟩ ⟨b,k,false⟩=pact p a b k:=by rw [ladder_c hp a b _ _ hk.symm]; unfold pact; split_ifs<;>simp_all
lemma luxury (hp:p∈conf 3)(a b c d:Badge G): Rule p (β a * β b) (θ c) (θ d)=pact p a c 1 * pact p b d 2+pact p a d 2 * pact p b c 1:= by
 unfold Rule; rw [reads_three hp, copy_mul];simp only [β,θ,codeP,lit_4 hp]; rw [lux_n hp (p:=p) c d, pact_eq hp a c (by decide),pact_eq hp a d (by decide),pact_eq hp b c (by decide),pact_eq hp b d (by decide),mul_zero,zero_add]
lemma three_same (hp:p∈conf 3)(a b c d:Badge G): Rule p (β a*β b*β c) (θ d) 1=0 ∧ Rule p (β a*β b*β c) 1 (θ d)=0:= by
 simp only [Rule,reads_three hp,copy_mul, copy_one, θ, β,codeP, mul_one, lit_4 hp]; simp only [lux, if_true, zero_mul,zero_add,mul_zero, and_self]
lemma any_p (b:Bend G 3)(h:Bend G 3)(he:b.j=h.j): lux p b h=0:= if_pos he
lemma spend_pair (hp:p∈conf 3)(a b c d:Badge G) : Rule p (β a) (θ b) (θ c*θ d)=0 ∧ Rule p (β a) (θ c*θ d) (θ b)=0:= by
 simp only [Rule, reads_three hp,θ, β,copy_mul, codeP, ←mul_assoc,lit_4 hp]; constructor <;> (repeat rw [lux_n hp]) <;> ring
lemma one_u (hp:p∈conf 3)(c d:Badge G): Rule p (1:Trio G) 1 (θ c*θ d)=0 ∧ Rule p 1 (θ c*θ d) 1=0 ∧ Rule p 1 (θ c) (θ d)=0:= by
 simp only [Rule,reads_three hp,θ,copy_mul,copy_one,one_mul,mul_one,codeP, lit_2 hp]; exact ⟨lux_n hp ..,lux_n hp ..,lux_n hp ..⟩
end YM.RG11.FirstW.Branch
