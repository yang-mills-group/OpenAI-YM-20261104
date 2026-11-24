import YM.WilsonCoeffUV.Root.UV.StrictCount
/-!
# Canonical transfers reexpressed in chosen endpoint coordinate. Left bound for finer products (not naive forward in older direction). -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}

section curves
variable (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F) (p:h<D)(N m k:ℕ)(b:Bool)
def warp (i) := if b then relativeC A Ñ N (m+i) (k-i) else relativeF A Ñ N m i
-- read inverse matrix gem after substituting local field Y in old reporting or new reporting. No extra affine factor.
def topGear (i:ℕ):Coil F := Chars F (warp A Ñ N m k b i) ((Jacob A Ñ T p N (m+i))⁻¹)
def aftGear (i:ℕ): Coil F :=Chars F (warp A Ñ N m k b i) (Jacob A Ñ T p N (m+i))
def CurNames :Coil F := hillcrest (aftGear A Ñ T p N m k b) k
def bindingS :Coil F := steepen (topGear A Ñ T p N m k b) k
end curves
lemma ebbing (L:Theatre H T p e E W)(u:L.V.anchor≤m)(v:m+k≤N)(q:Bool):
    let A:=L.V.draws; let Ñ:=L.V.paid; IsUnit (CurNames A Ñ T p N m k q).det ∧ bindingS A Ñ T p N m k q=(CurNames A Ñ T p N m k q)⁻¹:=by
    intro A Q; let X:= aftGear A Q T p N m k q; let Y:= topGear A Q T p N m k q
    have hx i (p':i<k): X i*Y i=1:=by unfold X Y aftGear topGear; rw [← map_mul, Matrix.mul_nonsing_inv _ (stellarized (leaseN L (m:=m+i) (by omega) (N:=N) (by omega))),map_one]
    exact campsE X Y (fun i p=> Matrix.isUnit_det_of_right_inverse (hx i p)) (fun i p=> Eq.symm (Matrix.inv_eq_right_inv (hx i p)))
lemma blendS (H:Hol G)(T: SectionData F)(p:h<D)(e)(E W C':Credit)(b:Bool)(i:ℕ)(v:i≤e):
    let X:= CourseS.length (H:=H) (T:=T) (p:=p) (e:=e) (E:=E) (W:=W) (U':=C'); let A (j: CourseS H T p e E W C'):= topGear j.vols.draws j.vols.paid T p j.I.n j.spur (X j) b; let B (j:CourseS H T p e E W C'):= topGear j.vols.draws j.vols.paid T p j.I.N j.spur (X j) b
    CreditsS (rubP X CourseS.Age) (rubP X CourseS.cab) (fun n=>lineS (stairs X A n) i) (fun n=>lineS (stairs X B n) i):=by
    intro X B Q
    let y:=Bank.rub X CourseS.Age; let θ:=Bank.rub X CourseS.cab; have hc := CourseB H T p e E W C'
    have hp:Brite y θ:=⟨fun i=>hc.large _,fun i=>hc.dist _⟩
    let M (a:Jag X)(N):= Jacob a.cargo.vols.draws a.cargo.vols.paid T p N (a.cargo.spur+a.coin); let P (a:Jag X)(N):= warp a.cargo.vols.draws a.cargo.vols.paid N a.cargo.spur (X a.cargo) b a.coin
    let K (a:Jag X):=(loose a.cargo.vols.draws (a.cargo.spur+a.coin)).L
    have he (i:Jag X)(N)(t:i.cargo.I.b≤ N): leaseM (K i) F (lineS (M i N) 0):=by
       apply leaseN i.cargo.robe.arch; · exact i.cargo.root.trans (by omega)
       have hz:i.coin< i.cargo.length:= i.credit; have hx:i.cargo.spur+i.cargo.length≤ i.cargo.I.b:= i.cargo.far; omega
    let F' (a:Jag X):=M a a.cargo.I.n; let V (a: Jag X):=M a a.cargo.I.N
    have hh k (w:k≤ i): CreditsS y θ (fun n=>lineS (twinge X B n) k) (fun n=>lineS (twinge X Q n) k):= by
       have hr i (t:i≤k):CreditsS y θ (fun n=>lineS (F' n)⁻¹ i) (fun n=>lineS (V n)⁻¹ i):= CreditsS.pony (fun m u=> windowBounds H T p e E W C' (u.trans (by omega : i≤ e))) hp (fun i=> he i _ i.cargo.I.hd) (fun i=>he i _ i.cargo.I.hg)
       exact Chars.glide (A:=fun i=>P i i.cargo.I.n) (B:=fun i=> P i i.cargo.I.N) hp (fun i t=>edgeC H T p e E W C' (t.trans (by omega)) b) hr
    exact baron hc (fun i=>i.I.buySpan) hh (fun i=> saddleSwan (he i _ i.cargo.I.hd) (he i _ i.cargo.I.hg) _ _)
lemma cashier {x θ:U→ℝ}(p:Brite x θ){P Q:U→ Wall F}(h:CreditsS x θ P Q):∃ W:Credit,∀ v,∀ i j:Alma F,twain (W.buy (x v)) (θ v) (P v i j) (Q v i j):=by
    classical
    suffices hh:∀ s:Finset (Alma F×Alma F),∃ W:Credit,∀ v,∀ i∈ s,twain (W.buy (x v)) (θ v) (P v i.1 i.2) (Q v i.1 i.2) by obtain ⟨W,g⟩:= hh Finset.univ; exact ⟨W,fun v i j=>g v (i,j) (Finset.mem_univ _)⟩
    intro s
    induction s using Finset.induction_on with
    | empty=> exact ⟨Credit.unit,by simp⟩
    | @insert i s e ih=>
       obtain ⟨c,C,h,H⟩:= h i.1 i.2; let B:Credit:=⟨c,max C 1,le_max_right ..⟩; obtain ⟨W,G⟩:= ih; refine ⟨B.plus W,fun v u hu=>?_⟩; have hx:=p.large v; have hy:=p.dist v; rcases Finset.mem_insert.mp hu with p|p; · subst u; exact ((H v).lift (le_trans (show _≤ B.buy _ from mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg (zero_le_one.trans hx) c)) (Credit.thickens _ hx)) hy)
       exact (G v u p).lift (Credit.thickened _ hx) hy

theorem glacier (H:Hol G)(T: SectionData F)(p:h<D)(e)(E W C':Credit)(b:Bool)(i:ℕ)(v:i≤e): ∃ C:Credit,∀ a: CourseS H T p e E W C', let V:=a.vols; let P (N:ℕ):= bindingS V.draws V.paid T p N a.spur a.length b; ∀ j k: Alma F,twain (C.buy a.I.Age) a.I.cab (lineS (P a.I.n) i j k) (lineS (P a.I.N) i j k):=by
    obtain ⟨Z,e⟩:= cashier ⟨fun a=>a.cargo.I.warm,fun _=>(trail_pos ..).le⟩ (blendS H T p e E W C' b i v); exact ⟨Z,fun a=>e ⟨a,a.length,le_rfl⟩⟩
end YM.WilsonCoeffUV.Cosmos
