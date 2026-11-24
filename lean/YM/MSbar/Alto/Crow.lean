import YM.MSbar.Alto.Arity
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
lemma garnish (m:ℕ)(hv:m≤N)(C':ℝ)(hc:0 ≤ C')(hx:C'≤ K.α (A.a.clock.J m)/2)(hs:Premier (main (A.a.S.side m p) (A.a.params m).clip (A.kin.path N m)))(b:ℕ)(w:ℝ)(hw:0<w) : Tin (Measuring.chart (A.a.S.side m p) G) C' s b w (ink (A.a.S.side m p) (A.a.params m).clip (A.kin.path N m)) (w^2*quota K (A.a.clock.J m) s):=by
   let i':= A.a.clock.J m; let O:= A.M.H N m; let t:= K.α i'/2; have ht₀ := (K.alpha_pos i'); have hx':0<t:=by unfold t; positivity
   have H₁ : O.metric.strip (K.α i') (drift K i'):= Work.F08.strip_mono (A.plan.rows N m hv).2.1 le_rfl (by unfold drift; linarith only [le_abs_self (K.Ω i')]) -- unfold O not present
   exact chronos (A.kin.path N m) O (A.a.params m).clip (A.support.cap N m hv) (A.support.links _ _ hv) (h.sworn N m hv p) (A.plan.all _ _ hv _) hs H₁ ht₀.le hc (show t+C' ≤ K.α i' from (by unfold t; linarith only [hx,(show i'=A.a.clock.J m from rfl)])) hx'.le (zero_le_one.trans (low_earns _ s hx'|>.1)) (cone_pos K i' |>.le) (fun d=> low_earns t s hx'|>.2 _ (by positivity)) b hw
include hf Z F t
lemma dentist : Premier (main (A.a.S.side m p) (A.a.params m).clip (A.kin.path N m)):= pierce F t α P₄ P₁ P₀ v! (h.towns m p|>.1) hf ((A.support.critical N m p hm F).1) (A.support.classicalPart N m p hm F) -- binder t unavailable
variable (hB:E/((A.a.S.block m).val:ℝ) ≤ grain (A.a.params (m+1)).clip (A.a.clock.op m p).patch Z (K.α (A.a.clock.J (m+1))))
local notation "L"=> ((A.a.S.block m).val:ℝ)
include hp hj hE ht
lemma pricesB (τ:ℕ)(ψ:τ= k):0<w!:=by
    have hx:=stance A j i m N p h hm rfl rfl E s hE ht hj; have Ht: (P!).strip ρ (drift K j):=by
        have he:= hx.res [] (by simp); apply Work.F08.strip_mono he le_rfl; simp only [List.length_nil,add_zero,pow_one]; exact div_le_self (cone_pos ..|>.le) (by exact_mod_cast (A.a.S.block m).property)
    obtain ⟨he,hz⟩:= A.support.critical N m p hm F; have hq:= A.support.cap N (m+1) hm
    exact nectar F Z t (by rfl) A.valid.kernel (h.towns ..) P₁ α hq _ v! he hz (K.alpha_pos j) Ht (cone_pos K j|>.le) rfl
end YM.MSbar.Alto
