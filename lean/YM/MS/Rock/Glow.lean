import YM.MS.Rock.Doves
/-!
# Clearing Scout itinerants and spin stability for compact D cycles

Ext namespace uses exponential-in-Re only. m Mercury pointwise internal bp. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Path
open Momentum Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
open Metric
variable {G:Gauge}{I E F H J:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
 {m n k:ℕ}{z:UScale I}{a b : I→ℝ}{r:ℝ}{f g:ℂ→Mob G} {u:ℂ→ Rip G}
variable {D:Set ℂ}{A B:ℝ}
lemma tall_mint (h:1≤A)(hp:A≤B)(x:Town): mint A x≤mint B x:=rpow_le_rpow (by linarith:0≤A) hp ((show 0<2*(x:ℂ).re+1 from x.property).le)
lemma mint_mul (hx:1≤A)(hp:1≤B)(x:Town): mint (A*B) x=mint A x*mint B x:=Real.mul_rpow (by linarith:0≤A) (by linarith:0≤B)
lemma brightN (i:ℕ): scaleC bn 1 fun z:Town=> ‖2*((z:ℂ)-i)‖:= by
    refine ⟨2*(1+(i:ℝ)),by positivity,1, fun z x hx=>?_⟩
    change ‖2*((z:ℂ)-i)‖≤2*(1+_)*(1+|bn z|)^_*1; unfold bn; simp only [mul_one,pow_one,abs_of_nonneg (norm_nonneg _),norm_mul]; norm_num; have he:= norm_sub_le (z:ℂ) (i:ℂ); simp only [Complex.norm_natCast] at he; nlinarith [norm_nonneg (z:ℂ)]
variable {c: Bool} {s:ℂ}
lemma scouts_cycle (h:Scout f)(hv:TrackR u)(hc:∀ i∈Town,Ruddy c (u i))(hp:∀ i∈Town, Sturdy c (f i))(hB:1≤B)(he:∀ i∈Town,rock B (u i)): Scout fun i=>ocean i (u i) (f i) where
    sky:= Path.wind_he h.sky hv.sky Subset.rfl hp hc way
    price:= by
       obtain ⟨A,hA,ha⟩:= h.price; obtain ⟨U,hU,hp'⟩:= hv.price; have hu : 1≤U*A:= one_le_mul_of_one_le_of_one_le hU hA;
       obtain H:=compact_fin (Z:=fun x:Town=>x.val) (a:=mint A) (b:=mint U) brightN ha hp' (fun i=>i.property) hB (fun i=>he _ i.property) (fun i=>hp _ i.property) (fun i=>hc _ i.property) (fun i=>(mass_positive i (by linarith:0<U)).le)
       refine ⟨U*A*B,one_le_mul_of_one_le_of_one_le hu hB,?_⟩; convert H using 1; ext; rw [mint_mul hu hB, mint_mul hU hA]; rfl
lemma Town_nat (n:ℕ): (n:ℂ)∈Town:= by change 0<2*Complex.re (n:ℂ)+1; norm_num; positivity
lemma Scout.kB (h: Scout f)(hp: s∈Town): kPrice (f s):= by obtain ⟨A,hA,hV⟩:=h.price; exact fee hV ⟨s,hp⟩
lemma TrackR.kU (h:TrackR u)(hp:s∈Town): rPrice (u s):= by obtain ⟨A,hA,hV⟩:=h.price; exact fun m a b=> fastline (hV m a b) ⟨s,hp⟩
namespace Scout
variable {g:ℂ→Mob G}
-- generic transfer Sturdy by testing integer rows equality with reference full dim family S_m. Need beams and at all W (n ≥m) not just l target.
def Hear (F:ℂ→Mob G)(X:Mob G): Prop:=∀ m n,∀ (h:m≤n),∀ i:Legs (Shore G m), F n m i=X n (Arts.lift h i)
variable (Hv:Scout g) {X:Mob G} (hx: Hear g X)
include Hv hx
lemma flight (he:∀ m (K: Spin (L m)), within c K → beam (flagS K G) (X m)= X m){i:ℂ}(hc:i∈Town): Sturdy c (g i):= by
    constructor
    · intro m K hk; funext l; obtain h1:= Crow (fun i:Legs (Shore G m)=> Dove Hv m i) _ (sense (flagS K G)|>.reaches l); refine agree_w h1 (Dove Hv m l) ?_ hc; filter_upwards [eventually_ge_atTop m] with n hn; let L:= K.arch hn; have hl:= he n L (arch_steady hn K hk); rw [show g n m= _ from funext (hx m n hn), ← Spin.telescopeS hn K,hl] -- h orientation
    intro m n h l; refine agree_w (Dove Hv n (Arts.lift h l)) (Dove Hv m l) ?_ hc; filter_upwards [eventually_ge_atTop n] with n hn; rw [hx _ _ hn,hx _ _ (h.trans hn),lifts_link]
-- cycle
end Scout
open Scout
lemma heard (h:Scout f)(hv:TrackR u)(hc:∀ i∈Town,Ruddy c (u i))(hp:∀ i∈Town,Sturdy c (f i)): Hear (fun i=> ocean i (u i) (f i)) (fun m=> Arc.pitch m • Ccy (u m m) (f m m) (Px m)):= fun _ n ht i=> reg_proj (Scout.kB h (Town_nat n)) (TrackR.kU hv (Town_nat n)) (hp _ (Town_nat n)) (hc _ (Town_nat n)) ht i
lemma orbit (h:Scout f)(hv:TrackR u)(hc:∀ i∈Town,Ruddy c (u i))(hp:∀ i∈Town,Sturdy c (f i))(hB:1≤B)(he:∀ i∈Town, rock B (u i)) (x:ℂ)(hx:x∈Town): Sturdy c (ocean x (u x) (f x)):= by
   refine flight (scouts_cycle h hv hc hp hB he) (heard h hv hc hp) ?_ hx; intro m K hK;
   let A:= flagS K G; have h₀:=K.volume; let n:ℂ:= m; have he :=Town_nat m; have ht:= Pilot.leadC A h₀ K.turn.toHomeomorph.measurableEmbedding ((hc n he).turn m _ hK) (f n m) (theory (Scout.kB h he) (TrackR.kU hv he) m); rw [(hp n he).turn m K hK] at ht; rw [show A.beam ((pitch m) • Ccy (u n m) _ (Px m))= pitch m • A.beam (Ccy _ _ _) from (A.beam.restrictScalars ℝ).map_smul (pitch m) (Ccy _ (f n m) (Px m))]; exact congr_arg ((pitch m) • ·) ht -- ℂ linear not know ℝ
end YM.MS.Rock
