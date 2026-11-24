import YM.WilsonCoeffUV.Stable.SourceSend
/-!
# Top matching on every fixed horizon. `forecast` in units of reporting horizon. Applicable also to residuals queried after capture BEFORE projection from raw. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}{H: Hol G}{T:SectionData F}{p:h<D}{v: Rails h k u e}{E W K U':Credit} {R S: TowerS G D}

def Silt (X:Island F D)(P:TowerS G D): TowerS G D:= P- Shrine X (opal F P)
def queries (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(N k c m i:ℕ)(X:TowerS G D):= burden A Ñ T p N k c m i (Silt (Peaks A Ñ T p N c) X)
def tallyV (A: Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(N k c m:ℕ)(X:TowerS G D): Verse F:= opal F X+ boot A Ñ T p N k c m (c-m) (Silt (Peaks A Ñ T p N c) X)

lemma sifted(X:Island F D)(p:Shimmer X)(q:On k R)(v:h≤ k): On k (Silt X R) ∧ opal F (Silt X R)=0:= by unfold Silt; have hz:=Shrine_on X p (opal F R) v; refine ⟨q.diff hz,?_⟩; rw [On.read_sub _ q hz,Shrine_read X (opal F R) p,sub_self]
lemma release (L:Theatre H T p e E W)(X:TowerS G D)(u:m+i=c): queries L.V.draws L.V.paid T p N k c m i X=X-Shrine (Peaks L.V.draws L.V.paid T p N c) (tallyV L.V.draws L.V.paid T p N k c m X):=by
   let T':= Peaks L.V.draws L.V.paid T p N c; let Y:= Silt T' X; let A:= L.V.draws; let B:= L.V.paid; let V:= boot A B T p N k c m i Y; unfold queries burden; rw [u,breath_top,tallyV,show c-m=i by omega]; change X - _ - Shrine T' V=X-_
   have he: Shrine T' V= Shrine T' (opal F X+V)-Shrine T' (opal F X):=by rw [← Shrine_diff, add_sub_cancel_left]
   rw [he]; change X-_ - _= X-Shrine T' (opal F X+V); abel

-- input moment sector. arbitrary assigned demands valid schedules below. restrict to analytic unwrapped-alias Bends exists not priced.
structure CutsP (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit) where
   L : Torch H T p v E W K
   L' : ChorusLine H T p e E W U
   he : L'.arch=L.L
   m : ℕ
   i : ℕ
   b : ℕ
   N : ℕ
   M : ℕ
   ha : L.L.V.anchor≤m
   hc : m+i≤b
   hn : b≤ N
   hm : b≤ M
   pt : TowerS G D
   pt' : TowerS G D
   sp : On k pt
   sp' : On k pt'
   fuel : ℝ
   hf : 0≤ fuel
   toll j r: j≤e→ YieldP 0 1 u fuel (L.L.V.tempC (m+i) b) (pt.2 j r) (pt'.2 j r)

namespace CutsP
variable (t:CutsP H T p v E W K U')
abbrev ceilC:= t.m+t.i
abbrev vesselsC:= t.L.L.V
def windowC : WindowS G (e+1) E:= ⟨t.vesselsC,t.m,t.i,t.N,t.M,t.b,t.ha,t.hc,t.hn,t.hm⟩
abbrev Age:= t.windowC.Age
abbrev ax:= t.vesselsC.draws
abbrev tx:= t.vesselsC.paid
abbrev δm := t.vesselsC.tempC t.ceilC t.b
abbrev oldA:= t.vesselsC.y t.ceilC
abbrev ρ := t.vesselsC.tempC t.m t.ceilC
abbrev Ntop := t.L.L.lore t.N t.ceilC
abbrev Mtop := t.L.L.lore t.M t.ceilC
lemma reach : t.vesselsC.anchor≤ t.ceilC:= t.ha.trans (by unfold ceilC; omega)
lemma tag : t.vesselsC.y t.ceilC≤ t.Age:= t.windowC.covers (show t.i≤ t.i from le_rfl)
lemma price0 (j:Alma F)(q:i≤ e) : twain (coinQ F v.sup D*t.fuel) t.δm (coeff i (opal F t.pt j)) (coeff i (opal F t.pt' j)):=by simp only [opal,coeff_mk]; exact foreQ _ (trail_pos ..).le F v.sup (fun i j q _=> t.toll i j q) j q
lemma priceT : ∃ C:ℝ,0≤ C∧∀ i≤ e,∀ j,YieldP 0 1 u C t.δm ((Silt t.Ntop t.pt).2 i j) ((Silt t.Mtop t.pt').2 i j):=by
    obtain ⟨V,H⟩:= Creed_more H T p e u E W; let P:= V.buy t.Age; let A:= ((Fintype.card (Alma F)*(e+1):ℕ):ℝ)*2*P; let B:=coinQ F v.sup D; have hb:0≤B:= coinSoar ..; have hx:0≤ P:= zero_le_one.trans (V.purchase t.windowC.warm); have hh:0≤ A:= by unfold A; positivity
    refine ⟨_,add_nonneg t.hf (mul_nonneg hh (mul_nonneg hb t.hf)),fun i z j=>?_⟩;
    let R:= t.L.L; have h (j' i h):= (H R t.ceilC t.b t.N t.M i t.reach t.hc t.hn t.hm h j' j).step (V.elder (t.vesselsC.depth _ t.reach) t.tag) (trail_pos ..).le
    exact (t.toll i j z).diff (tenderPV t.Ntop t.Mtop e j P (fun j' h i=> t.price0 i h) (fun x t i=> h i x t) hx (mul_nonneg hb t.hf) (trail_pos ..).le z)
-- used expenses
omit t in
lemma PriceSale : ∃ V:Credit,∀ t:CutsP H T p v E W K U',∀ i≤ e,∀ j,YieldP 0 1 u (V.buy t.Age *t.fuel) t.δm ((Silt t.Ntop t.pt).2 i j) ((Silt t.Mtop t.pt').2 i j):=by
    let C:ℝ:=((Fintype.card (Alma F)*(e+1):ℕ):ℝ)*2*coinQ F v.sup D
    have hh:= coinSoar F v.sup D; obtain ⟨V,h⟩:= Creed_more H T p e u E W; let X:= Credit.unit.plus ((pur C).prodC V); refine ⟨X,fun t i z j=>?_⟩
    let P:= V.buy t.Age; have hx:0≤ P:= zero_le_one.trans (V.purchase t.windowC.warm); have hf:= t.hf; have hδ:0 ≤ t.δm:= (trail_pos ..).le
    let U:=t.L.L; have ht (j' i v):= (h U t.ceilC t.b t.N t.M i t.reach t.hc t.hn t.hm v j' j).step (V.elder (t.vesselsC.depth _ t.reach) t.tag) hδ
    refine ((t.toll i j z).diff (tenderPV t.Ntop t.Mtop e j P (fun j' v i=> t.price0 i v) (fun x t i=> ht i x t) hx (mul_nonneg hh hf) hδ z)).step ?_ hδ
    apply le_trans _ (mul_le_mul_of_nonneg_right (Credit.fuel Credit.unit ((pur C).prodC V) t.windowC.warm) hf); rw [Credit.unit_cost, Credit.products, add_mul,one_mul]; apply add_le_add_right; apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pure_goal C _) hx) hf); exact le_of_eq (by unfold C; ring)

def hueAge (t:CutsP H T p v E W K U'):= (PriceSale (U':=U') (H:=H) (T:=T) (v:=v) (p:=p) (W:=W) (E:=E) (K:=K)).choose.buy t.Age
lemma org (t:CutsP H T p v E W K U'):0 ≤ t.hueAge*t.fuel:= mul_nonneg (zero_le_one.trans (Credit.purchase _ t.windowC.warm)) t.hf

def chest (t:CutsP H T p v E W K U') : Chest H T p v E W K U':= ⟨{
                                          L:=t.L
                                          m:=t.m
                                          c:=t.ceilC
                                          b:=t.b
                                          N:=t.N
                                          M:=t.M
                                          X:= Silt t.Ntop t.pt
                                          Y:= Silt t.Mtop t.pt'
                                          wealth:= t.hueAge*t.fuel
                                          ha:=t.ha
                                          hv:=by unfold ceilC; omega
                                          ht:=t.hc
                                          hn:=t.hn
                                          hm:=t.hm
                                          ex:=by
                                               have H:=sifted t.Ntop (production t.L.L (t.hc.trans t.hn) t.reach).1 t.sp v.hk; exact ⟨H.1,H.2,t.org,fun i j q=> ((PriceSale (U':=U') (p:=p)).choose_spec t i q j).wax⟩
                                          ey:=by
                                               have H:=sifted t.Mtop (production t.L.L (t.hc.trans t.hm) t.reach).1 t.sp' v.hk; exact ⟨H.1,H.2,t.org,fun i j q=> ((PriceSale (U':=U') (p:=p)).choose_spec t i q j).wane⟩
                                          rate:=fun i j q=> ((PriceSale (U':=U') (p:=p)).choose_spec t i q j).toll },t.L',t.he⟩
lemma cupped : t.chest.quest.Age ≤ t.Age:=by
    apply le_of_eq; unfold Age CourseS.Age WindowS.Age; change t.vesselsC.y t.m+ (t.vesselsC.draws.S.scale (t.m+ (t.ceilC-t.m))-t.vesselsC.draws.S.scale t.m)+ (t.ceilC-t.m:ℕ)=_; rw [show t.ceilC-t.m=t.i from by unfold ceilC; omega]; rfl
end CutsP
end YM.WilsonCoeffUV.Shard
