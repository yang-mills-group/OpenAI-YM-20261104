import YM.MSbar.Alto.Crow
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}
open Supply Input
variable {O:ChartRatio G}{K:MapPrices} {B: Sheet G}{D: Rolls B}{Θ:Protection D}{T:Delays Θ}{W: Bar T}{I:Wait W}{P:PostCost D}(A:Directed G I O K P)
local notation "B₀"=> A.kin
local notation "ℓ"=> A.a
set_option quotPrecheck false
local notation "Θ₀"=>A.a.clock
variable (m N k p:ℕ)(s:ℕ)
local notation "M!"=> (A.a.S.block m).val
local notation "g!"=> A.a.S.side m p
local notation "g'"=> A.a.S.side (m+1) p
local notation "ε!"=> A.a.clock.op m p
local notation "Q"=> A.M.towers N m
local notation "P!"=> (A.M.towers N m).A0
local notation "q"=> A.a.params m
local notation "u"=> A.a.params (m+1)
local notation "α"=> A.kin.path N (m+1)
local notation "P₄"=> A.kin.path N m
local notation "i"=> A.a.clock.J m
local notation "j"=> A.a.clock.J (m+1)
local notation "P₀"=>(A.a.params m).clip
local notation "P₁"=>(A.a.params (m+1)).clip
variable (F:Forest (A.a.clock.op m p).ratio) (h:Merit A.a A.M) (hm:m<N)
variable (Z:Uniform.Before G (A.a.params (m+1)).width (A.a.params (m+1)).paths (A.a.clock.J (m+1)) B.kernel (k+3)) (x:G.ColorIndex) (t:(A.a.clock.op m p).Choices)
local notation "v!"=> A.kin.stationary N m p F
local notation "ρ"=> K.α (A.a.clock.J (m+1))
local notation "w!"=> grain P₁ (A.a.clock.op m p).patch Z ρ
local notation "b!"=> tango K j i s k (A.a.clock.op m p).patch O Z w! (Z.tables P₁ (A.a.clock.op m p).patch)
variable {z:ℕ}{w D₁ E a:ℝ}(hp:6≤ s)(hf:Premier (main (A.a.S.side (m+1) p) (A.a.params (m+1)).clip (A.kin.path N (m+1)))) (hj:5≤ A.a.clock.J (m+1))(hE:0≤E)(ht: E ≤ ceilα K (A.a.clock.J (m+1)) (A.a.clock.J m))
include h hm
variable (hB:E/((A.a.S.block m).val:ℝ) ≤ grain (A.a.params (m+1)).clip (A.a.clock.op m p).patch Z (K.α (A.a.clock.J (m+1))))
local notation "L"=> ((A.a.S.block m).val:ℝ)
variable (hw:0 <w)(hD:E/((A.a.S.block m).val:ℝ) ≤ D₁)(hD':D₁≤ K.α (A.a.clock.J (m+1))/2)
variable (hC:10*(z+4)< ((A.a.S.side m p).val))(hc:Fintype.card PlaqAxes *((A.a.params m).paths*(A.a.params m).paths*url (A.a.S.side m p) z (A.a.params m).width)≤1)
include hp hf hj hE ht hB hw hD hD' hC hc
lemma ready : SceneB (Alto.tango K j i s k (ε!).patch O Z w! (Z.tables P₁ (ε!).patch)) F t P! O v! α P₁ P₄ P₀ k s E D₁ w x :=by
    have hh : w! = w!:=rfl -- lex `!=`
    have hP:= stance A j i m N p h hm rfl rfl E s hE ht hj; let X:=ceilα K j i; have hl:1 ≤ L:=by exact_mod_cast (A.a.S.block m).property
    have he:=A.support.cap N (m+1) hm
    obtain ⟨hn,hy⟩:=A.support.critical N m p hm F
    have hs:=pricesB A m N k p s F h hm Z t hp hf hj hE ht k rfl; have hl':0 ≤ E/L:=div_nonneg hE (by positivity)
    have hx: low w! s ≥1:= low_earns w! s hs|>.1
    refine ⟨hP,hD,?_,?_,?_,?_,(show 2 ≤ ↑(A.a.S.block m) from (Nat.le_trans (by omega : 2 ≤ 3) (A.a.S.block_large m))),hy,hn⟩
    · have Ht:(P!).strip ρ (drift K j):=by have ht:= hP.res [] (by simp); apply Work.F08.strip_mono ht le_rfl; simp only [List.length_nil,add_zero,pow_one]; exact div_le_self (cone_pos ..|>.le) hl
      exact spends F Z t (by rfl) A.valid.kernel (h.towns ..) P₁ α he _ v! hn hy (K.alpha_pos j) Ht (cone_pos ..|>.le) rfl (zero_le_one.trans hx) (fun d=>low_earns w! s hs|>.2 _ (by positivity)) hl' hB
    · intro r hr d hd
      let X':= pinK j G X k s (ε!).patch O Z; have hX:0≤X':=by unfold X' pinK; positivity
      by_cases he:d=0
      · subst d; unfold fuelTest; rw [_root_.map_sub, splitK,splitK,sub_zero]; exact ⟨hX,fun i'=>by rw [map_zero]; exact Quote.nill hX⟩
      obtain ⟨d',rfl⟩:=Nat.exists_eq_succ_of_ne_zero he; have hf:= billing (s:=s) F Z O t A.valid.kernel (h.towns m p) A.ratio X (snag r) d' (by omega) (zonepos K j i|>.le); apply Tokew.delta (Tokew.soft hf ((div_le_self hE hl).trans ht) hl') le_rfl; let U(d):= |cream X s d (ε!).patch Z O|; let D₂:= ∑ i'∈Finset.range k,U i'; change _ ≤ 1+D₂; apply (le_abs_self _).trans; apply (Finset.single_le_sum (f:=U) (fun x _=> abs_nonneg _) (Finset.mem_range.mpr (by omega : d'<k))).trans; exact le_add_of_nonneg_left zero_le_one
    · intro r hr; exact ⟨garnish A m N p s h hm m hm.le E hE (ht.trans (le_trans (min_le_right ..) (min_le_right ..))) (dentist A m N k p F h hm Z t hf) _ w hw,garnish A m N p s h hm (m+1) hm D₁ (hl'.trans hD) hD' hf _ w hw⟩ -- signatures
    have hg': |grossH (rim (collectT g! P₄ P₀)) (sun G x)+2|≤1:= (sampled (sun G x) _ _ (A.support.cap N m hm.le) z hC (sunny x)).trans hc -- Midpoint.rim?
    rw [caliper,LinearMap.comp_apply, ion P₄ P₀ (dentist A m N k p F h hm Z t hf)]; change 1 ≤ |grossH _ (sun G x)|; apply le_trans _ (neg_le_abs _); linarith only [(abs_le.mp hg').2]
end YM.MSbar.Alto
