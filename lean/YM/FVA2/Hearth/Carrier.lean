import YM.FVA2.Hearth.Planet
/-!
 # Fk.read of any unmasked slot assembly at prescribed Laurent degrees

 `A` any occupant in `Entry T` with real Taylor data (includes arbitrary smooth at
 0, though physical Prescription uses primitive nonlinear cylinder lifts). Keep support
 addresses when using these: there is an explicit template (one ordered tag lists and
 shared valuation). `Fk.psi` below reads exactly from that template, namely all the
 occupied warm coordinates and a price along the open `y` ray. Instantiate with the
 actual stencil `rad T O` to identify the physical answer, and with arbitrary product
 Rail tickets in case one's producer uses `Silk.price`. No deletion or bar/coincident
 convention on tags; in particular the theorem about a complete product observable uses
 this reading ON THAT PRODUCT. Common high-order `N` may be higher than publication
 order to support output shifting; equality to symbolic full mass rather than a witness
 concealing overhead costs.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade RGComparison.Core16 PowerSeries
open RGComparison.Core16.Lumen RGComparison.Core16.Forge
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{n:Side}{L:Fabric G n}(T:Cloth L)(y:Flats G (Bottom L))
variable (x:G.ColorIndex)(w:L.Accounts→ℝ→ℝ)

 def tease : Lumen.Stuff G (Warm T) (Option (Warm T)) := (fun i=> i.elim (Sum.inr (Lumen.colors G x)) Sum.inl)
 def readRay (u: Option (Warm T)→G.Color) : ℝ × Facade.Panel T := (u none x, fun i=> Lumen.axis.symm (u (some i)))
 def lens (A:Entry T→ℝ) := A ∘ flank y ∘ readRay T x
lemma badgeLoc (A : Entry T→ℝ): Contains T y (tease T x) (lens T y x A) A:= by
 let F:= Fk.Door G (Warm T)
 let f i (v:F):G.Color:= v.2 i
 let e:= Lumen.axis (G:=G)
 have he: 0∈e.source:= ContDiffAt.mem_toOpenPartialHomeomorph_source ..
 have hF:∀ᶠ v:F in 𝓝 0,∀ i,Lumen.axis.symm (Lumen.turn (f i v))= f i v:= eventually_all.mpr fun i=> ((show Continuous (f i) from (continuous_apply i).comp continuous_snd).tendsto 0).eventually (e.open_source.mem_nhds (show f i 0 ∈ e.source from he)) |>.mono (fun v hv=>e.left_inv hv)
 filter_upwards [hF] with v hv; change A ((flank y) (readRay T x (Fk.scene (tease T x) v))) = A ((flank y) v); apply congr_arg (A ∘ flank y) (Prod.ext (xseat x _) (funext <| fun i=>hv i))

-- regular for interested Fk exterior consumers, but even passing THIS doesn't assert qualification of motion.Lo.O
lemma readRay_warm {A:Entry T→ℝ}(h:ContDiffAt ℝ ∞ A 0): ContDiffAt ℝ ∞ (lens T y x A) 0:= by
 have he:ContDiffAt ℝ ∞ (readRay T x) 0:= by
     refine ContDiffAt.prodMk ?_ ?_
     · exact (EuclideanSpace.proj x:G.Color →L[ℝ] ℝ).contDiff.contDiffAt.comp _ (contDiffAt_apply ℝ _ none _)
     exact contDiffAt_pi.mpr fun i=> (Lumen.axis_hot (G:=G)|>.of_le le_top).comp (f:=fun v:Option (Warm T)→ G.Color=>v (some i)) _ (contDiffAt_apply ℝ _ (some i) _)
 let a:= (flank (E:=Facade.Panel T) y)
 have hv: readRay T x 0=0:= Prod.ext rfl (funext fun i=>Lumen.axis_zero)
 exact (show ContDiffAt ℝ ∞ A ((a ∘ (readRay T x)) 0) from by rw [comp_apply,hv,map_zero]; exact h).comp _ ((LinearMap.toContinuousLinearMap a).contDiff.contDiffAt.comp _ he)

variable {J:ChartRatio G} (hj:LocalRatio J) (z:L.Accounts→PowerSeries ℝ)(hz:∀ i,0<term (z i) 0)
variable (N:ℕ)(hw:∀ i,ContDiffAt ℝ ω (w i) 0)(h:∀i,Through N (Facade.amount (w i)) (z i))
local notation "P"=> localClimate T y x w
variable (O:Wilson.Config G n→ ℝ)(hO:PreTest O)
local notation "V"=> rad T O
local notation "q"=> collared T z hj hz
local notation "Ξ"=> Stack.read y (Prod.snd (drive T (z ∘ some) (headquarters z) (imprintRoot O) J q))
include hO hz hj h hw

lemma predicts : Through N (PowerSeries.mk (Fk.valuation P J (tease T x) (lens T y x V))) Ξ:= by
 rw [← follows T z hz hj, aligns T O hO]; apply accredited T y x w hj z hz N hw h (badgeLoc T y x V) (stamp_hot T O hO)
lemma predicted (d i:ℕ)(hi:d+i≤N): Fk.read P J (tease T x) (lens T y x V) d i=coeff (d+i) Ξ:= by rw [←predicts T y x w hj z hz N hw h O hO (d+i) hi,coeff_mk]; rfl
omit hO h hw hz
omit hj in
private lemma payClimate {t:ℝ}(hr:t≠0) : (P).expect t (fun u=> attending L O (committed T y t u)) = (Burn T w y O t)/(Burn T w y 1 t):= by
 unfold Planet.expect Planet.pot Burn; let v:=((P).bureau t); let g(u):= attending L O (committed T y t u); let μ:= Chart.physical G (Warm T); let d:= Module.finrank ℝ (Facade.Panel T)
 have hA(u): income T w y O t u= Real.exp (-1)*(v u*g u):= by unfold income; rw [climates T y x w t hr, Pi.smul_apply]; change g u * (_* v u)=_; ring
 have hx(u):income T w y 1 t u= Real.exp (-1)*v u:= by unfold income; rw [climates T y x w t hr, Pi.smul_apply]; exact one_mul _
 change (∫ x,v x * g x ∂μ)/(∫ x,v x∂μ)= ( (t^d)⁻¹ * ∫ x,income T w y O t x∂μ)/ ((t^d)⁻¹ * ∫ x,income T w y 1 t x∂μ); simp_rw [hA,hx,integral_const_mul];
 rw [mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero _ hr)),mul_div_mul_left _ _ (Real.exp_pos _).ne']
-- Actual conditional aspiration for coherent physical clock readings. strictly after fixing everything.Order `N` only on output-coeff reading.
include hO h hw hz hj
lemma in_planet (hm:∀ i,Measurable (w i)): Aspiration (fun t=> (P).expect t (fun u=> attending L O (committed T y t u))) (Fk.valuation P J (tease T x) (lens T y x V)):= by
    let s := hot T y O hO hj; let U:= Fk.harvest P J (tease T x) (lens T y x V); let b := Fk.birth P J
    let K:= Facade.raise (Facade.rate T) w y; have hh:Laplace.Steep K:= steep T z hz w y hw N h; have hg:= fun i=> (hw i).continuousAt; have hp := zeroWeight w z hz N h
    have ho : Tracks (Burn T w y O) (constit T w y J (rad T O)):= aspirations T w y O hO hj hg hp hh hm
    have he: Tracks (Burn T w y O) (PowerSeries.mk U) := (launch_me T y x w (badgeLoc T y x V)).symm ▸ ho -- inspect
    have hb: Tracks (Burn T w y 1) (PowerSeries.mk b):= by
        unfold b; rw [launch_vacant]; exact aspirations T w y 1 one_register hj hg hp hh hm -- syntax
    unfold Tracks at he hb; rw [Tracks.asTerm] at he hb
    let v:= divide U b; have hi:Aspiration ((Burn T w y O)/(Burn T w y 1)) v:= he.quotient hb (feasible T y x w hj z hz N hw h).ne';
    suffices hh: Tracks (fun t=> (P).expect t (fun u=> attending L O (committed T y t u))) (PowerSeries.mk v) from (by unfold Tracks at hh; rw [Tracks.asTerm] at hh; exact hh)
    exact (show Tracks ((Burn T w y O)/(Burn T w y 1)) (PowerSeries.mk v) from by unfold Tracks; rwa [Tracks.asTerm]).patch (Tested.eventually_pos.mono (fun t ht=> (payClimate T y x w O (ne_of_gt ht)).symm))
end YM.FVA2.Hearth
