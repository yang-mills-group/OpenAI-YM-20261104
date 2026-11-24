import YM.FVA2.Generator.Hygro
import YM.FVA2.Generator.Harmony
/-!
# Prepare the Cast estimates for the first-order check

Keep the $x ≠ 0$ qualification on the point estimates! See `Generator/Port`
about their use for the scale-generator check at order one.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Prices
open Function Set Filter XSpace Pages Center XSpace.Litter XSpace.Scale XSpace.Trace XSpace.Lows XSpace.Mu XSpace.Chart2 RG12.Strike Lattice XSpace.Sail XSpace.Tide Further.FreeCovariance.KP
open Exterior Hygro Playpen XSpace.Drama Circuits Polynomial
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{n k d:ℕ}
abbrev Glow:= E4→ Polynomial ℂ
abbrev deco (d:ℕ)(v:ℂ) :Glow:= fun _=> monomial d v
def outgoing (q:Addr G)(p:Bond G):Glow:= fun x=> monomial 0 (Hygro.high q p x)
def static (B:Hat G d) (v:Fee G):ℂ:=∑ i:Fin (d+1),if i.val=v.k then (↑(probe v.line (release (B i).val)):ℂ) else 0
def upcharge (B:Hat G d)(q:MultiplierEstimates G):=(q.map (fun i=>static B i.fee)).prod
def rugged (B:Hat G d)(p:Bond G): Glow:= fun x=> ∑ i:Fin (d+1), monomial (1+i.val) (screen B p i x)
-- spells: used for subpieces here too
variable {ι:Type}{a:ι→ℝ} {L:Filter ι} (S:Tendsto a L (𝓝 0))(h:∀ᶠ i in L,0<a i) (B:Hat G d)
structure Cast (p:Tile G)(n:ℕ)(a:ι→ℝ)(L:Filter ι)(B:Hat G d)(Q:Glow) : Prop extends Icon a L d n p B Q where
    book : Book G n p
lemma Cast.times {Q R:Tile G}{x y:Glow}{B: Hat G d}(p:Cast Q n a L B x)(q:Cast R k a L B y): Cast (Q*R) (n+k) a L B (x*y):=by
    refine ⟨⟨fun t z h=>?_⟩,Book.mul p.book q.book⟩; rw [Pi.mul_apply,bins,eval_mul]; refine ((p.reach t z h).mul (q.reach t z h)).congr fun i=>?_ ; rw [Pi.mul_apply,map_mul,map_mul,pow_add]; ring
-- now positions
include h S
local notation "a%%" n "," t:max=> (↑t:ℂ)⁻¹^(n:ℕ)
private lemma fixed (t:ℝ)(p:Fee G)(i:Fin (d+1)):
    Tendsto (fun j=> a%% p.cost,(a j) *((↑(t*a j):ℂ)^(1+i.val) * ↑(probe p.line (release (B i).val)))) L (𝓝 ( (if i.val=p.k then ↑(probe p.line (release (B i).val)) else (0:ℂ)) * (t:ℂ)^p.cost)) :=by
    let u:= probe p.line (release (B i).val); split_ifs with ht
    · refine tendsto_const_nhds.congr' ( h.mono fun j hj=>?_ ); have he:(a j:ℂ)≠0:=by exact_mod_cast hj.ne'
      push_cast; rw [mul_pow,show 1+i.val=1+p.k from by omega]; unfold Fee.cost; rw [inv_pow]; field_simp
    by_cases hx: p.k ≤ i.val; swap; · rw [show probe p.line (release (B i).val)=0 from caned_early p.due (lt_of_not_ge hx) _]; simp [tendsto_const_nhds] -- alpha
    let n:=i.val-p.k; have hu:0<n:=by unfold n; omega
    obtain he:= ((( Complex.continuous_ofReal.continuousAt.tendsto.comp S ).pow n).mul_const ((t:ℂ)^(1+i.val)*(u:ℂ))); simp only [Complex.ofReal_zero,zero_pow hu.ne',zero_mul] at he; rw [zero_mul]; refine he.congr' ( h.mono fun j hj=>?_ ); have he'(z:ℂ)(h:z≠0) : z^(1+i.val)= z^p.cost*z^n:=by rw [← pow_add]; congr 1; unfold n Fee.cost; omega
    push_cast; change _ = _⁻¹^_*(((↑t:ℂ)*(↑(a j):ℂ))^_*_); rw [mul_pow, he' (↑(a j):ℂ) (by exact_mod_cast hj.ne'),inv_pow]; unfold Function.comp u; field_simp [ show (a j:ℂ)≠0 by exact_mod_cast hj.ne' ]
lemma once (p:Fee G): Cast (fun _=> harp p.line) p.cost a L B (deco p.cost (static B p)) := by
    refine ⟨⟨fun t z hz=>?_⟩,Book.left _⟩; simp_rw [music_at,scenic_break, leg_test,map_sum,Complex.ofReal_sum,map_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]; rw [deco,bins,eval_monomial]; simp_rw [static, Finset.mul_sum, Finset.sum_mul]; apply tendsto_finsetSum; intro i _; exact fixed S h B t p i
lemma entering (p:MultiplierEstimates G) : Cast (Pages.left p) (wage p) a L B (deco (wage p) (upcharge B p)) := by
    induction p with
    | nil=> refine ⟨⟨fun t z _=>?_⟩,Book.unit⟩; change Tendsto (fun i=> _^(0:ℕ)* _ ) L (𝓝 (bins (monomial 0 1) t)); simp [bins, show ∀ x:Cover, Pages.left (G:=G) [] x=1 from fun x=>rfl, tendsto_const_nhds]
    | cons i p ih=> obtain he:=(once S h B i.fee).times ih; rw [show deco i.fee.cost (static B i.fee) * deco (wage p) (upcharge B p) = deco (wage (i::p)) (upcharge B (i::p)) from funext fun x=> monomial_mul_monomial .. ] at he; exact he
lemma rents (p:Bond G)(q:Addr G): Cast (gem q p) (p.fee.cost+q.cost) a L B (outgoing q p):=by
    refine ⟨⟨fun t z hz=>?_⟩, Nat.add_comm q.cost p.fee.cost ▸ Book.rent q.fee p.fee⟩; rw [outgoing,bins,eval_monomial,pow_zero,mul_one]; simp_rw [music_at]; refine (attaches S h (marks z S h) hz p q).congr fun i=>?_ ; simp [gem,pit]
private lemma remote (p:Bond G)(m:Fin (d+1))(x:E4): Tendsto (fun j=> (a j:ℂ)⁻¹^p.fee.cost * (a j:ℂ)^(1+m.val)*(↑(probe (displace (mark (a j) x) p.fee.line) (release (B m).val)):ℂ)) L (𝓝 (screen B p m x)):= by
    let u:=((B m).val p.j); let V:=(paint p.color); obtain he := tendency S h p.k (p:= fun j=> mark (a j) x) (half p.j) (u:=fun _=> u) (A:=u) x tendsto_const_nhds (marks x S h); rw [Exterior.pigment]
    refine ((V.continuous.continuousAt.tendsto).comp he).congr' (h.mono fun i hi=>?_ ); rw [Function.comp_apply,map_smul,map_smul,← Litter.peaked,map_smul (peak ..),Pi.smul_apply,map_smul]; unfold Bond.fee; dsimp only; rw [Trace.toll,Trace.pin,in_gate]; unfold V; rw [dyes, Complex.real_smul, Complex.real_smul]; simp only [radius,add_zero]; rw [show ∀ y:Cover,peak p.k (feed (half p.j) u) y=crack p.k (XSpace.Scale.twig p.j (release (B m).val)) y from fun y=> congr_fun (peaked ..) y]; push_cast; unfold Fee.cost; dsimp only; rw [pow_add (a i:ℂ),pow_add ((a i:ℂ)⁻¹)]; field_simp [ show (a i:ℂ)≠0 by exact_mod_cast hi.ne' ]
lemma rising (p:Bond G): Cast (Pages.right p) p.fee.cost a L B (rugged B p):=by
    refine ⟨⟨fun t z _=>?_⟩,Book.right _⟩; simp_rw [ music_at, scenic_break, Pages.right, leg_test, map_sum,Complex.ofReal_sum, map_smul, smul_eq_mul, rugged,bins,eval_finsetSum ]; simp_rw [ Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_mul, mul_pow, eval_monomial, Finset.mul_sum ]; apply tendsto_finsetSum; intro i _; refine ( (remote S h B p i z).mul_const _ ).congr (fun j=>?_ ); ring
end YM.FVA2.Generator.Prices
