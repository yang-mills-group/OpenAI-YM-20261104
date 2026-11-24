import YM.MSbar.Geneva.Cash
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue RawP JetTab Bristol
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}{ι:Type}{X:ι→ℝ}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop)
variable {p m k:ℕ}(P:Patch)(j:ℕ)(M: StageCost)(hp:G.Simple)
local notation "L"=> (P.L.val:ℝ)
local notation "d" i=> tip G P.L (X i)
local notation "μ" i=> goalP (d i) p
local notation "a" i=> αm (X i)
local notation "ν" i=> Cane.value (αm (X i)) M.C M.A M.E M.s M.sway
local notation "w" i=> vol (d i)
local notation "W" i=> hull (X i)
noncomputable def climbP (P:Patch)(M:StageCost)(i:ℕ) := let l:ℝ:= P.L.val; 5*4^(i+1)*(l^4*(Cane.value 0 M.C M.A M.E M.s M.sway/l)^(i+1))
noncomputable def plotP (P:Patch)(M:StageCost)(i:ℕ) := let l:ℝ:= P.L.val; 4^(i+1)* (l^4*(Cane.value 0 M.C M.A M.E M.s M.sway/l)*(2*(feed 0 M.A M.E M.C M.s M.sway i/l^i)*(4/l)^(4-i))*5) -- 4+ dims
include hp hX
private lemma vessel:Tendsto (fun i=>ν i) φ (𝓝 (Cane.value 0 M.C M.A M.E M.s M.sway)):=((show Continuous (fun x=>Cane.value x M.C M.A M.E M.s M.sway) from (by unfold Cane.value Cane.candle Measuring.factor; fun_prop)).continuousAt.tendsto.comp (Geneva.ray hX))
lemma climbs : Tendsto (fun i=> (W i)^(j+1)*( (5*(μ i))/(w i)^(j+1)*L^4*((ν i)/L)^(j+1))/goalP (X i) p) φ (𝓝 (climbP P M j)):=by
    let g(i):=goalP (d i) p/goalP (X i) p; have hg:Tendsto g φ (𝓝 1):= (Run.shift hX hX G hp P.L (pawn p)).2
    have he := ((footingX hX P.L hp).pow (j+1)); have h' := ((vessel hX M hp|>.div_const L).pow (j+1)); have hp:= (((hg.const_mul 5|>.mul he).mul_const (L^4)).mul h')
    have hv:5*1*(4:ℝ)^(j+1)*L^4*(Cane.value 0 M.C M.A M.E M.s M.sway/L)^(j+1)=climbP P M j:=by unfold climbP; dsimp only;ring
    rw [hv] at hp; refine hp.congr (fun i=>?_); unfold g; ring
lemma slopeB {v t b:ι→ℝ}{c:ι→Side} (he: j∈Finset.Icc 1 3)(hh:∀ᶠ i in φ, hatW (d i)^4 ≤ (c i).val) (hv: Van φ X v) (ha:Run φ X t (-(1/2))) (ht:Run φ X b 0)(d':ℝ): Tendsto (fun i=> (W i)^(j+1) *slopeW (v i) (t i) 0 d' (b i) (5*(goalP (d i) p)) (w i) p j (c i) G /goalP (X i) p) φ (𝓝 0) :=by
     let u:=fun i=> d i; let e:=pawn p; let V(i):= goalP (X i) p; let S(i):=goalP (u i) p
     have hx:= Run.shift hX hX G hp P.L (pawn p)
     have hm:Tendsto (fun i=> ((c i).val:ℝ)^ (3:ℕ)) φ atTop:= (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_mono' φ hh ((tendsto_pow_atTop (by norm_num)).comp (Alto.broad.comp hx.1)))
     let Wx(i):=W i; have hW':Run φ X Wx 0:=((Run.stanza hX|>.mulY hX ((32:ℝ)⁻¹)).mulK hX 4); have hs: Run φ X S (pawn p) := (Run.wander hX G hp P.L (pawn p) _).2 (Run.core hx.1 _); have ht'(f0:ι→ℝ)(ht:Tendsto f0 φ atTop):True:= trivial -- remove
     have hD:Tendsto (fun i=> (Wx i)^(j+1)*v i/V i) φ (𝓝 0):=(Run.Ycost hX (hW'.Ypow hX _) (hv (pawn p-1))|>.dory hX (by linarith only))
     have hR : Tendsto (fun i=> (Wx i)^(j+1)*tumbler (c i) (5*S i/(w i)^(j+1))/V i) φ (𝓝 0):=by
          have ht:= ((show Tendsto (fun i=>S i/V i) φ (𝓝 1) from hx.2).mul ((footingX hX P.L hp).pow (j+1))|>.const_mul (5*100^3)); refine (ht.div_atTop hm).congr (fun i=>by unfold Wx; unfold Midpoint.tumbler; ring)
     by_cases hp:j=1
     · have hz:= hD.add (hR.const_mul 100) |>.const_mul 64; simp only [mul_zero,add_zero] at hz; refine hz.congr (fun i=>?_); unfold Bristol.slopeW Bristol.coal; rw [if_pos hp]; subst j; unfold Wx; unfold Midpoint.tumbler V S u;ring -- measure
     let f(i):= Bristol.toll (t i) 1 d' (5*S i) (b i) p (j-1) G
     have h : Run φ X f (epsW p):=by
          unfold f Bristol.toll; apply Run.addR hX ?_ ?_
          · let p'(x):=fCost d' (t x) 1 0; have hz : Run φ X p' (-(1/2)):= by unfold p' fCost; simp only [Nat.zero_add,pow_one,one_pow,mul_one]; exact Run.mulY hX ha _
            apply Run.loosen (Run.mulR hX ((hz.mulK hX _).mulY hX _) (hs.mulK hX _)); unfold epsW; linarith only
          apply Run.count hX (Finset.range (p+1)) (fun n i=> t i^n*(2*fCost d' (t i) 1 (p-n)*solo (j-1) G*b i)); intro i hi; unfold fCost; simp only [one_pow,mul_one]; apply Run.loosen (((ha.raise hX _).mulR hX (((((ha.raise hX _).mulY hX _).mulK hX _).mulY hX _).Yrat hX ht)))
          rw [←mul_add,←Nat.cast_add (R:=ℝ),show i+(p-i+1)=p+1 by have ht:=Finset.mem_range.mp hi;omega];push_cast; linarith only [(mp0 p).1]
     have hP:= (hR.const_mul 4).add ((Run.Ycost hX (hW'.Ypow hX (j+1)) h).dory hX (mp0 p).2.1); rw [mul_zero,add_zero] at hP; refine hP.congr (fun i=>?_); unfold slopeW;rw [if_neg hp]; unfold Wx f Midpoint.tumbler S V u goalP; ring
lemma volumeP {v t b:ι→ℝ}{c:ι→Side} (he: j∈Finset.Icc 1 3)(hh:∀ᶠ i in φ, hatW (d i)^4 ≤ (c i).val) (hv: Van φ X v) (ha:Run φ X t (-(1/2))) (ht:Run φ X b 0)(d':ℝ): Tendsto (fun i=>volumeY G M.s j (4-j) M.sway M.C M.A (αm (X i)) M.E P 0 (w i) (W i) (5*(goalP (d i) p)) (slopeW (v i) (t i) 0 d' (b i) (5*(goalP (d i) p)) (w i) p j (c i) G) /goalP (X i) p) φ (𝓝 (plotP P M j)):=by
    let v₀:=slopeW; let f₁(i):= (W i)^(j+1)*slopeW (v i) (t i) 0 d' (b i) (5*(μ i)) (w i) p j (c i) G/goalP (X i) p
    have hT:Tendsto f₁ φ (𝓝 0):=slopeB hX P j hp he hh hv ha ht d'; let Ω:=fun x=> Cane.value x M.C M.A M.E M.s M.sway; let B(x):=2*(feed x M.A M.E M.C M.s M.sway j/L^j)*(4/L)^(4-j); have hb : Tendsto (fun i=>B (αm (X i))) φ (𝓝 (B 0)):= (show Continuous B from by unfold B feed Cane.value Cane.candle Measuring.factor; fun_prop).continuousAt.tendsto.comp (Geneva.ray hX)
    let s:= (crownB G M.E M.A M.C M.sway/L)^j; have hh:= ((Run.shift hX hX G hp P.L (pawn p)).2); let f0(x:ℝ):= L^4*(Ω x/L); have hx:Tendsto (fun i=>f0 (αm (X i))) φ (𝓝 (f0 0)):= ((vessel hX M hp).div_const L).const_mul (L^4); have hu:= hx.mul (((hb.mul ((footingX hX P.L hp).pow (j+1))).mul (hh.const_mul 5)).add (hT.const_mul s))
    have he: f0 0 * (B 0 * 4^(j+1)*(5*1)+s*0)=plotP P M j:=by unfold plotP B f0 Ω; dsimp only;ring
    rw [he] at hu; refine hu.congr (fun i=>?_); unfold volumeY; unfold f0 f₁ B Ω goalP s; unfold Mosaic.ξy; ring -- ring
noncomputable def shortCash (G:Gauge)(i:ℕ)(C D α:ℝ)(wc v l σ:ℝ) := stepW 0 C * D /v^(i+2)*l^4*(σ/l)^(i+1)
lemma sFire (d':ℝ): Tendsto (fun i=> (W i)^(j+1)*(shortCash G j d' (5*(μ i)) (αm (X i)) (W i) (w i) L (ν i)) /goalP (X i) p) φ (𝓝 0):=by
     let s0(x):= (ν x); let U(i):= 5*(μ i); let f(x):= goalP (X x) p; let v(x):=w x
     have hu : Tendsto v φ atTop:= ((Alto.broad.comp ((Run.shift hX hX G hp P.L 1).1)).atTop_mul_const (r:=(32:ℝ)⁻¹) (by positivity)); have h:= climbs hX P j M hp (p:=p); have hx:= h.const_mul (stepW 0 d') |>.div_atTop hu; apply hx.congr; intro i; unfold shortCash v; ring
end YM.MSbar.Geneva
