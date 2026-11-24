import YM.MS.Vista.Court
/-!
# The trace component of the clock. Include quadrature difference on straight unshifted part only.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}[NormedAddCommGroup E][NormedSpace ℝ E]{S:Scale I}
 {K L:I→Latch.Edge G}{X Y:I→Law G}{h x y:I→ℝ}{A:I→Cover}{μ ν:I→Measure QP}{n:ℕ}{p c:Bool}{w:Wire (BH G) E QP}
abbrev moneyL (c:Bool): QP→L[ℝ] QP:= if c then ContinuousLinearMap.id .. else -ContinuousLinearMap.id ..
lemma walkL (p:Bool)(x:QP): moneyL p x= Opp p x:= by cases p <;> rfl
abbrev HoopT (S:Scale I)(w:Wire ( BH G ) E QP)(a b:I→ℝ):= (fun p=> Qbud w S ( positive S 4 a b ) p)
def lineWork (b:Bool)(K:I→Latch.Edge G)(X:I→Law G)(w:Wire ( BH G ) E QP)(t:I)(z:QP× E):= payF b K X (sail w z.2) t z.1
lemma Hath (j k:BH G)(hw:Course c w)(ht:p=true→ c=false)(hx:Lens c S X x (w.length+2))(hf:Sheet S h K): pole S ( fun i (z:QP×E)=> K i j k z.1 * X i ((j,z.1)::(k,Opp p z.1)::sail w z.2) ) (HoopT S w h x):= by
    let P:= ContinuousLinearMap.fst ℝ QP E; let L:=Wire.lift w ( ContinuousLinearMap.snd ℝ QP E ); let T:= moneyL p ∘L P; let Q:Wire ( BH G ) ( QP× E ) QP:= (j,P)::(k,T)::L; have hL : Course c Q:= by
        cases h:p; · intro hz; change net Q=0; unfold Q L T; simp [ h,moneyL,hw hz ] -- `net` simp
        exact ( ht h ) ▸ ( fun v=>Bool.noConfusion v : Course false Q)
    obtain he :List.length Q=w.length+2:= by simp only [Q,L,lift_len,List.length_cons]
    convert! ( Rapid.mul ( hf j k |>.rapid (F:=E) ) ( hx ( QP× E ) Q he hL ) ) using 1
    · ext; simp [ Plane.Chart,Q,L,T,P,walkL ]
    funext i; unfold HoopT Qbud positive pitch Q L; rw [field_cons, field_cons,field_lift]; rw [show S.length i ^4=S.length i^(4:ℤ) from rfl]; calc
       _= S.length i ^ ((4:ℤ)+fieldDim wfield w)*( h i * x i ):= by rw [ zpow_add₀ ( S.pos i ).ne' ]; ring
       _ = _ := by rw [show (4:ℤ)+fieldDim wfield w=(4-wfield j-wfield k)+(wfield j+(wfield k+fieldDim wfield w)) from (by omega), zpow_add₀ ( S.pos i ).ne' ]; ring
lemma grass (hw:Course c w)(ht:p=true→ c=false)(hx:Lens c S X x ( w.length +2))(hf:Sheet S h K)(hv:nn h)(hX:nn x): pole S (lineWork p K X w) ( HoopT S w h x ):= by
    refine topCycle.allFin _ (fun i _=> topCycle.allFin _ (fun j _=> Hath i j hw ht hx hf) ?_) ?_ <;> exact pos_nn _ (np S hX hv 4) S -- namespace?
-- estimate.$L.
def pClock (μ:I→Measure QP)(p:Bool)(A:I→Cover)(K:I→Latch.Edge G)(X:I→Law G)(i:I):= Θ_pc p (μ i) (A i) (K i) (X i)
lemma p_price (he:VistaQ S μ ν)(hp:Fund S K h)(hv:Visible X): Plane.Chart (pClock μ p A K X) w=waveInt (fun i=> be (A i)) ν ( lineWork p ( tinted K ) X w ):= funext fun i=>funext fun _=> portPC he hp hv i p _
omit [NormedSpace ℝ E] [NormedAddCommGroup E] in
lemma Cash (i:I)(x y:I→ℝ)(w:Legs (Mode ( BH G ) E )): S.length i^pitch w*positive S 4 x y i * fee S i= S.length i^pitch w * (x i*y i) := by unfold positive fee; field_simp [(S.pos i).ne'] -- fee.S namespace optional
lemma p_pay (he:VistaQ S μ ν)(hp:Fund S K h)(hv:Visible X)(ht:p=true→ c=false)(hx:Lens c S X x (n+2))(hh:nn h)(hX:nn x): Lens c S ( pClock μ p A K X ) (h*x) n:= by
    intro E _ _ w hw hew; unfold Cape; rw [ p_price he hp hv ]; obtain hx:= grass hew ht (hw ▸ hx) (tint hp) hh hX; convert! ( Wavepay ( U:=fun i=> be ( A i ) ) (fun i=> sailor _) he.sector hx ( he.mint E ) ) using 1; exact funext fun i=> ( ( Cash (S:=S) i h x w )|>.symm ) -- Goals Eq positions.F.Param
lemma p_remote {v:I→ℝ}(hp:Radar S v A ν)(he:VistaQ S μ ν)(H:Fund S K h)(hv: Visible X)(ht:p=true→c=false)(hx:Lens c S X x (n+2))(hh:nn h)(hX:nn x)(k:ℕ): Lens c S ( pClock μ p A K X ) (fun i=>h i*x i*(S.length i/v i)^k) n:= by
    intro E _ _ w hw hV; unfold Cape; rw [ p_price he H hv ]; convert ( hp E _ _ ( grass hV ht (hw ▸ hx) (tint H) hh hX ) k ) using 1; ext i; -- shadow
    change S.length i^pitch w*( _ * _ )= _; rw [ ← mul_assoc, show HoopT S w h _ i * fee S i=_ from Cash ..] -- arg
-- no μ assumptions for diff except.In.Progress. Let quadrature.B.point frame. characteristic `Θ_pc false 0`; step canonical.Hyp.Index.Side full
variable {N:I→Side}
lemma SectorG {f:I→QP×E→ℂ}(hp:∀ i,S.length i≤(N i).val)(hf:pole S f x)(j:ℕ): Bound S ( Sugar (ψstep∘ N) f ) (fun i=> x i*fee S i*(S.length i/(N i).val)^j):= by
    have he (p:I): S.length p * (ψstep ∘ N) p = tier * ( S.length p/ ( N p ).val ):= by unfold Function.comp ψstep; ring
    obtain hx:= Osc.Snap.funds hf (b:=ψstep ∘ N) (fun i=>ψpp _) rising.le (ν_engine hp) j; refine hx.raise ⟨ tier^j,pow_pos rising _,0,fun i p h=> ?_⟩; apply le_of_eq; dsimp only; rw [he,mul_pow]; ring
lemma p_diff (hp:∀ i,S.length i ≤ ( N i ).val)(hf:Fund S K h)(he: Visible X)(hv:Lens c S X x (n+2))(hh:nn h)(hX:nn x)(j:ℕ): Lens c S ( pClock (fun i=>σcap ( N i )) false 0 K X - pClock (fun _=> μzone) false 0 K X ) (fun i=>h i*x i * ( S.length i /( N i ).val )^j ) n:= by
    intro E _ _ w hL hV; obtain hx:= grass (X:=X) hV ( fun h=> Bool.noConfusion h : false=true→ c=false ) (hL ▸ hv) (tint hf) hh hX; unfold Cape; rw [show Plane.Chart (pClock _ _ _ _ _ - _) w = Sugar (ψstep ∘ N) (lineWork false ( tinted K ) X w) from ?_ ]; swap; · rw [show Plane.Chart (pClock _ _ _ _ _ - _) w= Plane.Chart (pClock (fun i=>σcap ( N i )) false 0 K X) w-Plane.Chart (pClock (fun _=> μzone) false 0 K X) w from rfl, p_price ( f_cap hp ) hf he, p_price (routineQ S) hf he ]; ext i p; unfold Sugar TreeSum waveInt; simp [ show ∀ i:QP,be 0 i=1 from (fun _=> by simp [ be,show embed 0=0 from (by ext; simp [embed])]) ]; rfl
    convert SectorG ( f:=lineWork false (tinted K) X w ) hp hx j using 1; ext i; rw [show HoopT S w h x i * fee S i=_ from Cash ..]; ring -- syntax
end YM.MS.Vista
