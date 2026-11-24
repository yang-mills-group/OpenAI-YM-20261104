import YM.RGLocalTaylor.Retain.Parade
/-!
# Purchase inherited response & operations with the F witness.Estate
May combine its upgrade with arbitrary analytic purchase Decal farther
before initializing. Needed ALL periods & Books at once.Power estimate.
Proof based on `Awning` & `Mayer.Calendar`, `Time.Opening`. Keep
costs proportional to e norms relative to allowance, across representation
reclosure. Need `Spring.result` boards to use the callbacks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Trees
open PhysicalNext.Repeat.Daisy.Charity.RG12
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
namespace Retain
open RG01.Survive
open Mayer goodK Mill Fort
namespace Gala
variable {θ K : ℝ}

lemma rates4 (P:Teller G)(Q : YM.ConnectedActivityE6.Target G P)(L : Side) (Γ : Target.Expense Q) (hw: Γ.wanting ≤ -(7/16:ℝ))
   (j l M D : ℕ) (θ:ℝ) {μ δ:ℝ} (hμ:0<μ) {u f α : ℝ→ℝ} (hu:Rate G L 0 u) (hf:Rate G L 0 f) (hr:Rate G L 0 α) (cost : ℝ):
   let p:= arcRadius G L; let z x:= Mill.hill Q L μ x (f x) (u x) (α x) θ (p x) j l M
   ∀ᶠ x in atTop, degreePrice (radiusB x) (γprice Q L x μ) Q.δ ≤1/2 ∧
      degreePrice (radiusB x) (creditStencil M θ (p x) * γprice Q L x μ) Q.δ ≤1/2 ∧
      degreePrice (radiusB x) (Laminate.width Q μ L x) Q.δ ≤1/2 ∧
      degreePrice (radiusB x) (z x) δ ≤1/2 ∧ cost*(collars G δ x j D*(z x*(1-1/2)⁻¹)) ≤ 1 ∧
      collars G δ x j D *(z x*(1-1/2)⁻¹) ≤1 := by
   intro p z; let a:= Mayer.height; have hp: Rate G L a p:=Rate.power
   have hS: 0 ≤ a:= by norm_num [a,Mayer.height];
   have ht: a+Q.rate<0:= by unfold a Mayer.height; linarith [Γ.reach]
   have hg : Rate G L Q.rate (Q.goal L) := Rate.power; let t x:=creditStencil M θ (p x)
   have ht': Rate G L a t := (((hp.mul_left _).mul_left _).mul_left _)
   have hW : Rate G L Q.rate (Laminate.width Q μ L) := (Q.rate_root L hμ).add (hg.add (hg.mul_right _)); let V x:= Fort.γprice Q L x μ; have hF:Rate G L Q.rate V:= hW.add hg
   have hR: Rate G L (a+Q.rate) (fun x=> t x * γprice Q L x μ):=ht'.mul hF
   have hk: Rate G L (a+Q.rate) (fun x=> Mill.account Q L μ x (l+j) (t x)):= by
      simpa only [Mill.account,Reserves.treeYield,pow_zero,mul_one] using! ((hR.mul_right (1-1/2)⁻¹).mul_left (Reserves.extract Q.ε (l+j) 0 0))
   have hJ: Rate G L 0 (fun x=> speedBill (f x) (u x) (α x) j):= by
      simpa only [zero_mul,zero_add] using! hf.mul ((((Rate.const 1).add hu).add (hr.mul_left 2)).pow j)
   have hz: Rate G L (a+Q.rate) z:= (hg.weaken (le_add_of_nonneg_left hS)).add (by simpa only [zero_add] using! (((hJ.mul_right ((2:ℝ)^j)).mul_right ((M+2:ℝ)*2)).mul hk))
   have he : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
   have hp : Rate G L 0 (fun x=>collars G δ x j D):=by simpa only [zero_mul] using! ((he.pow (D*j)).mul_right (Reserves.polyPrice δ (D*j)))
   have hu:=hp.mul (hz.mul_right (1-1/2)⁻¹); have hT :0+(a+Q.rate)<0:=by rw [zero_add]; exact ht -- type?
   filter_upwards [(Mayer.rate0 G L _ _ hF Q.δ).below Q.stop (1/2) (by norm_num),(Mayer.rate0 G L _ _ hR Q.δ).below ht (1/2) (by norm_num),(rate0 G L _ _ hW Q.δ).below Q.stop (1/2) (by norm_num),(rate0 G L _ z hz δ).below ht (1/2) (by norm_num),(hu.mul_left cost).below hT 1 zero_lt_one,hu.below hT 1 zero_lt_one] with x ha hb hc hd he hz
   exact ⟨(le_abs_self _).trans ha,(le_abs_self _).trans hb,(le_abs_self _).trans hc,(le_abs_self _).trans hd,(le_abs_self _).trans he,(le_abs_self _).trans hz⟩

-- ratio to actual δE(pressureClock b=>true, NO cost replacing betaF path exotic)
abbrev mantle_rim (G:Gauge)(L:Side)(x:ℝ):= betaF G x L ^(1/4:ℝ)
def dividend (G:Gauge)(P:Stage)(x:ℝ) : ℝ:= Time.credit G P* δE x/64
lemma rpay0 (G:Gauge)(L:Side)(p:Stage){f:ℝ→ℝ}(q:ℝ)(hq:Rate G L q f)(hh:q < -(11/10:ℝ)) : ∀ᶠ x:ℝ in atTop, f x ≤ dividend G p x := by
   let A:=Time.credit G p /64; have ha:0<A:= div_pos (Time.credit_pos ..) (by norm_num)
   filter_upwards [Delay.shift_pos G L, eventually_gt_atTop (0:ℝ),Sienna.contraction G L (a:=1) ha hq hh] with x h hB ht
   unfold dividend; rw [mul_div_right_comm]; apply le_trans (b:= A*δE (betaF G x L))
   · have he : δE (betaF G x L)=betaF G x L^(-(11/10):ℝ):=by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg h.le,← Real.rpow_mul h.le]; norm_num
     rw [he]; exact (one_mul (f x)) ▸ ht.le
   unfold δE; apply (mul_le_mul_of_nonneg_left ?_ ha.le); apply Real.rpow_le_rpow (by unfold Clock.gap; positivity) ?_ (by norm_num); exact inv_anti₀ (Real.sqrt_pos.mpr hB) (Real.sqrt_le_sqrt (le_add_of_nonneg_right (Work.E04.shift_nonneg G L)))

variable (G)
set_option quotPrecheck false
-- unused cleanup
local notation "O" => Chi.canonical
structure Heavings (p:Stage)(G:Gauge)(L:Side)(s:ℝ):Prop where
   live : 1≤ Mayer.arcRadius G L s
   scale : 1 ≤ vest G L s
   heft : 1 ≤ mantle_rim G L s
   benefit : 0 < dividend G p s
   unmark : (Mayer.arcRadius G L s^2)⁻¹*(1 / vest G L s) ≤ dividend G p s
   special : ((Mayer.arcRadius G L s * mantle_rim G L s))⁻¹*(1 / vest G L s) ≤ dividend G p s
   margin : (Mayer.arcRadius G L s^3)⁻¹ ≤ dividend G p s

lemma bear (P:Stage)(L:Side) : ∀ᶠ x:ℝ in atTop, Heavings P G L x:=by
   have he (a:ℝ): Rate G L (-a) (fun x=> (betaF G x L ^ a)⁻¹):=Rate.power.congr (by filter_upwards [Delay.shift_pos G L] with x hx; exact (Real.rpow_neg hx.le a).symm)
   let p:= arcRadius G L; let B:= mantle_rim G L; let C:= vest G L;
   have hp :Rate G L (- Mayer.height) (fun x=>(p x)⁻¹):= he _
   have hv:= he (9/16:ℝ); let g x:=(C x)⁻¹; let b x:=(B x)⁻¹; have ht : Rate G L (-(1/4:ℝ)) b := he _
   filter_upwards [(Work.E09.betaF_growth G L).eventually_ge_atTop 1,rpay0 G L P _ ((hp.pow 2).mul hv) (by norm_num [Mayer.height]), rpay0 G L P _ ((hp.mul ht).mul hv) (by norm_num [Mayer.height]), rpay0 G L P _ (hp.pow 3) (by norm_num [Mayer.height]), eventually_gt_atTop (0:ℝ)] with x hx ha hv hh hX
   constructor
   · exact Real.one_le_rpow hx (by norm_num [Mayer.height])
   · exact Real.one_le_rpow hx (by norm_num)
   · exact Real.one_le_rpow hx (by norm_num)
   · exact div_pos (mul_pos (Time.credit_pos ..) (Real.rpow_pos_of_pos (Clock.gp hX) _)) (by norm_num) -- context name?
   · simpa only [one_div,inv_pow] using! ha
   · rw [mul_comm (arcRadius ..),_root_.mul_inv_rev,one_div]; exact hv
   simpa only [inv_pow] using! hh

-- Quoted combined Customer.Upfront quantization
variable {G}
set_option quotPrecheck false
local notation "b'" => Mayer.arcRadius G L s
structure Threads (H: Cash W s μ L Q o C T R) (N:Captain H j C' d v Y A b r B q n O) (uJ vJ e d₁ K θ:ℝ)(δ g budget turn:ℝ)(k l M power:ℕ):Prop where
   ht : Awning H N.conduit A b d₁ e uJ vJ k l
   pos : 0<δ
   width : g+δ+δ ≤ Q.exp
   health : 1≤Mayer.arcRadius G L s
   approved : Approved K θ j M
   vote : Q.goal L s≤ K
   effort : Mayer.arcRadius G L s * Q.goal L s ≤1
   check' : degreePrice (radiusB s) (γprice Q L s μ) Q.δ ≤1/2
   checkK : degreePrice (radiusB s) (creditStencil M (bead θ M) (Mayer.arcRadius G L s) * γprice Q L s μ) Q.δ ≤1/2
   fuzzy : degreePrice (radiusB s) (Laminate.width Q μ L s) Q.δ ≤1/2
   noteH : budget = Mill.hill Q L μ s e uJ (patchPrice r vJ M) (bead θ M) (arcRadius G L s) j l M
   checkE : degreePrice (radiusB s) budget δ ≤1/2
   price' : turn * (collars G δ s j power*(budget*(1-1/2)⁻¹)) ≤ 1
   priceMark : collars G δ s j power*(budget*(1-1/2)⁻¹) ≤ 1

def Gates (H:Cash W s μ L Q o C T R)(δ g budget turn:ℝ)(j M power:ℕ):Prop := Fort.Upkeep P Q L s ∧ ∃ (uJ vJ e d₁ K θ A b C' d v Y r B q:ℝ)(k l n:ℕ)(N:Captain H j C' d v Y A b r B q n Chi.canonical), Threads H N uJ vJ e d₁ K θ δ g budget turn k l M power

def checkpoints (P:Teller G)(Q: YM.ConnectedActivityE6.Target G P) (Γ:Target.Expense Q) (L: Side) (W μ:ℝ)(o:Target.Order G W)(D:RG.Stage)(i:ℕ)(x:ℝ) :=
   Heavings D G L x ∧ (∀ M≤ i, ∃ budget, ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Stamp T→∀ (R:Rep G f)(C:ℝ)(H:Cash W x μ L Q o C T R), Gates H (Height.asset Γ) Γ.earn budget (Height.away D) D.order M D.power)

lemma earned (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(Γ: Target.Expense Q) : ∃ n, ∀ L:Side,n≤L.val→∀ W μ o D i, Γ.wanting≤ -(7/16:ℝ)→0<W→0<μ→∀ᶠ x:ℝ in atTop, checkpoints P Q Γ L W μ o D i x:= by
   obtain ⟨n,h⟩:= Awning.available P Q; obtain ⟨m,hm⟩:= Fort.rents Q
   refine ⟨max n m,fun L hL W μ o D i hw hW hμ=>?_⟩
   apply (bear G D L).and; let T₁ (M:ℕ)(x:ℝ)(b:ℝ):= ∀ (c f:Side)(S:StepData c f)(T:Tube G S),Stamp T→∀ (R:Rep G f)(C:ℝ)(H:Cash W x μ L Q o C T R), Gates H (Height.asset Γ) Γ.earn b (Height.away D) D.order M D.power
   suffices H:∀ M:ℕ,∀ᶠ x in atTop,∃ v,T₁ M x v from (eventually_all.mpr fun M:Fin (i+1)=> H M).mono (fun x hx z hz=> hx (⟨z,Nat.lt_succ_of_le hz⟩:Fin (i+1)))
   intro M
   by_cases ht:∃ D:Patch,D.Branches P.bind G∧D.L=L∧D.J=P.j
   swap; · exact Eventually.of_forall fun x=> ⟨0,fun c f S T _ R C H=> let h:=H.laws.data.funds; False.elim (ht ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩)⟩
   obtain ⟨Δ,hd,hL',hD⟩:=ht; let j:=D.order
   obtain ⟨a,b,C,q,r,e,uJ,vJ,v,w,t,B,k,l,hr,he,hu,hV,_,hX⟩:= h L ((le_max_left ..).trans hL) (M+1) Δ hd j Chi.canonical W hW μ hμ o
   obtain ⟨K,θ,hK⟩:= Mayer.approved j M; let α x:=patchPrice (r x) (vJ x) M; let w':= Height.asset Γ; let A:= Height.away D; let v' x:= Mill.hill Q L μ x (e x) (uJ x) (α x) (bead θ M) (Mayer.arcRadius G L x) j l M
   have hz: Rate G L 0 α:= (hr.mul_left _).add (hV.mul_right _)
   filter_upwards [hX,rates4 (δ:=w') P Q L Γ hw j l M D.power (bead θ M) hμ hu he hz A, first_rates (δ:=w') P Q L Γ hw j l M D.power hμ hK hu he hz A,hm L ((le_max_right ..).trans hL)] with x hx hf hv h₀
   refine ⟨v' x,fun c f S T ht R C' H=>?_⟩; obtain ⟨N,hS⟩:= hx c f S T ((H.laws.data.funds).patch hL' hD) ht R C' H
   have hP:Γ.earn + w'+w' ≤ Q.exp:= by unfold w' Height.asset; linarith
   obtain ⟨ha,hv,hp,-⟩:=hv -- maybe indent
   obtain ⟨hb,hK',hf, ht',hx,hy⟩:=hf
   exact ⟨h₀,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,N,⟨hS,Height.asset_pos _,hP,ha,hK,hv,hp,hb,hK',hf,rfl,ht',hx,hy⟩⟩

def decal (G:Gauge):Decal G:= ⟨checkpoints,earned⟩
end Gala
end Retain
end YM.RGLocalTaylor
