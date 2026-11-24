import YM.WilsonComparison.Finite.Reexpress
import YM.MS.Tide.Coi

/-!
# One normalized Wilson moment algorithm for unscaled kernels and calibration columns

All the markers live in a common universe W. Re-express the **same** top bare variable
in the value of every term. A polynomial/tensor list of field choices uses the supplied
physical stencils, with arbitrary coefficients (complexification allowed; works in
particular for real fee menus). Equality to `PhysicalSum` here is for Landau moment.
Combine later with the actual Orb tree-saddle prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonComparison.Finite
open Function Finset Precision Lattice
open MS MS.Landau MS.Swirl MS.Swirl.Near MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Native MS.Book
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors
open MS.Book.Convolve MS.Book.Program MS.Native.Wilsonian
open MSBar Barr Bric Inlay Odom
open PowerSeries (coeff)
open scoped BigOperators Classical Topology
variable {G:Gauge}{χ:ChartRatio G}{n:Side}{W E:Type} [AddCommGroup E][Module ℂ E]
local notation "B"=>broadcastSeries
local notation "K"=>Master G n true
local notation "R"=>PermV (σbranch (G:=G) (n:=n))
variable (h:LocalRatio χ)

lemma burn (k:ℕ) : B (landauInteraction h n) k = if k=0 then 0 else SendB G n true (core G k):= by
  change broadcastSymbol _ =_; rw [landauInteraction,PowerSeries.coeff_mk]; split; exact map_zero _; exact priceRank h k
lemma broadcast_nil : B (landauInteraction h n) 0=0:= by rw [burn]; rfl
lemma report_stencil (k:ℕ) (x:Stencil G k) (A c : Cover): B (columnSeries (x.pace n (A+c)))=pointL ℕ (Mark_T G n A c) (levels k x.F):= by
  funext i; change broadcastSymbol (coeff i (columnSeries _))=_; rw [columnSeries,PowerSeries.coeff_mk]; exact x.same_source ..

variable (φ: Team)(y:ℝ)(A: Cover)
lemma adj_vac : NRG (Stripped φ) y n G true=
    substitute (shift φ y) (B (landauInteraction h n)):= by
  funext i; unfold NRG; by_cases he:i=0; rw [he,Book.Program.pay0, broadcast_nil]; rfl
  rw [if_neg he,style,strip_wobble, rules, rules,map_sum]; simp_rw [map_smul]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [burn]; split_ifs with ht; · rw [ht, Book.Program.cut,pow_zero, PowerSeries.coeff_one, if_neg he, zero_smul, smul_zero]
  rfl
abbrev adjustedV (x:PowerSeries (Cutis.Winter.LightQ G n ℝ)):= substitute (shift φ y) (B x)
-- rate weights read in reexpressed variable. Positions suppressed from a calibrated Column.
structure Letter (G:Gauge) where
  b : ℕ
  f : Stencil G b
  u : ℝ→ T ℂ
abbrev Multiplet (G:Gauge) := List (Letter G)
def reel (φ:Team)(x:Multiplet G): Actor G:= fun y=>
  (x.map fun p=> rates (Dot G Cover) (p.u y)
    (substitute (shift φ y) (levels p.b p.f.F))).sum
abbrev place (p:Letter G)(A c:Cover)(n:Side):= p.f.pace n (A+c)

lemma port (x:Multiplet G) (c:Cover) : pointL ℕ (Mark_T G n A c) (reel φ x y) =
    (x.map (fun p=> rates _ (p.u y) (adjustedV φ y (columnSeries (place p A c n))))).sum := by
  unfold reel; rw [map_list_sum]; simp_rw [List.map_map]; congr 1; apply List.map_congr_left; intro i _;
  rw [Function.comp_apply,pass_rate, show pointL ℕ (Mark_T G n A c) (substitute _ _) = _ from Book.Program.comm _ _ _, adjustedV,place,report_stencil]; rfl
lemma port_guard (x:Multiplet G)(c:Cover) : pointL ℕ (Mark_T G n A c) (reel φ x y) ∈ (R).guard:= by
  rw [port]; apply list_sum_mem; intro i hi; obtain ⟨w,_,rfl⟩:=List.mem_map.mp hi; exact rate_ok (actor _) _ (keep_guard _ (broadcast_guard _))

-- iterated multilinear extension (instead of Stamp-index sets and casts)
def exposed (F : List (Pace (deck n) G) → PowerSeries ℝ) (φ:Team)(y:ℝ)(A:Cover): List (Cover× Multiplet G) → List (Pace (deck n) G) → T ℂ
 | [],x=> substitute (shift φ y) (complex_coeff (F x))
 | (o,s)::l,x=> (s.map fun p=> Trunk.core (p.u y) (exposed F φ y A l (x++[place p A o n]))).sum

def shell (φ:Team) (y:ℝ)(A:Cover): List (Cover × Multiplet G) → SpecB (FixedMode G n)
 | []=>(R).unit
 | (o,x)::l => (R).core (pointL ℕ (Mark_T G n A o) (reel φ x y)) (shell φ y A l)

private lemma nodes (q:SpecB (FixedMode G n)) (s:List W) (V:W→SpecB (FixedMode G n))(Z:W→T ℂ) (h:∀ i,Endμ K σbranch q (V i) (Z i)) : Endμ K σbranch q (s.map V).sum (s.map Z).sum:= by induction s with| nil=>exact zeroEnd|cons i l ih=>exact sumEnd (h i) ih

lemma exposed_pay (l : List (Cover× Multiplet G)) (p:List (Pace (deck n) G)) : Endμ K σbranch (NRG (Stripped φ) y n G true)
    ((R).core (adjustedV φ y (p.map columnSeries).prod) (shell φ y A l)) (exposed (landauPrimary h) φ y A l p):= by
  induction l generalizing p with
  | nil=>
    rw [shell, (R).identityR,adj_vac h φ]; exact move_End (share φ y) (native_to_Endμ h _) (broadcast_nil h)
  | cons a l ih=>
    let q:=NRG (Stripped φ) y n G true; let S(p:List (Pace (deck n) G)):= adjustedV φ y (p.map columnSeries).prod; let Z:=exposed (n:=n) (landauPrimary h) φ y A l; let Y:=shell (n:=n) φ y A l
    obtain ⟨o,x⟩:=a; rw [shell,port]; unfold exposed; rw [show (R).core ((x.map _).sum) _= (R).core.flip Y ((x.map (fun p=> rates _ (p.u y) (adjustedV φ y (columnSeries (place p A o n))))).sum) from rfl]; simp_rw [map_list_sum, List.map_map]
    have he (v:Pace (deck n) G): S (p++[v])=(R).core (S p) (adjustedV φ y (columnSeries v)):= by unfold S; rw [List.map_append,List.prod_append,List.map_singleton,List.prod_singleton]; unfold adjustedV; rw [broadcast_mul]; exact (perm_hom (share φ y) (actor σbranch)).craft _ _
    apply nodes; intro k; let v:=place k A o n; let f:= k.u y
    change Endμ K _ q ((R).core (S p) ((R).core (rates _ f (adjustedV φ y (columnSeries v))) Y)) (Trunk.core f (Z (p++[v])))
    rw [← (R).star_a, right_rate (M:=actor σbranch), ← he, left_rate (M:=actor σbranch)]
    exact payEnd f (ih _)

variable [LinearOrder W]
-- weights + positions + marker order. allow W with duplicates of field value not tag
variable (v:W→Multiplet G)(c:W→Cover)
local notation "φq" => Marks (reel φ ∘ v) y n A c
lemma markerRight (s:Finset W): φq s∈(R).guard:= by
  by_cases hp:s.card=1; swap; · rw [mark_off hp]; apply Submodule.zero_mem
  obtain ⟨a,rfl⟩:=card_eq_one.mp hp; rw [mark_me]; exact port_guard φ y A (v a) (c a)

-- care instance diamonds DecidableEq W for Nodup
lemma font_eq (t:List W)(he:t.Nodup): Font σbranch (φq) t.toFinset=shell φ y A (t.map fun w=>(c w,v w)):= by
  induction t with
  | nil=>
    have ht : Happy (marked W) (φq):= mark_off (s:=∅) (by simp) _ _ _ _
    rw [Font,List.toFinset_nil]; exact Puff.Stencil.simple_E (R) _ _ ht
  | cons i l ih =>
    have ht:= List.nodup_cons.mp he; rw [List.toFinset_cons];
    rw [show Font _ _ _= _ from Puff.Stencil.cheers (R) (markerRight φ y A v c) (fun s h=> mark_off h y n A c) l.toFinset i (by simpa using ht.1),mark_me]; specialize ih ht.2; unfold Font at ih; rw [ih]; rfl

/-- End-to-end Landau input theorem prior to gauged alignment to the
    common PertExtension.Orb.diag tree report. Includes full normalization, even for positive marks,
    and the dependency of the coupling shift on the whole vacuum independent of tags. -/
theorem landau_physical (t:Finset W) : MS.Fleet.PhysicalSum G φ y n true t c A (reel φ ∘ v)
    (exposed (n:=n) (landauPrimary h) φ y A (t.toList.map fun w=>(c w,v w)) []) := by
  unfold Fleet.PhysicalSum; nth_rw 1 [← t.toList_toFinset]; rw [ font_eq φ y A v c t.toList t.nodup_toList]
  have he:= exposed_pay (G:=G) (n:=n) h φ y A (t.toList.map fun w=>(c w,v w)) []
  simpa [adjustedV,broadcast_one,show substitute (shift φ y) (R).unit=(R).unit from skin _ _,(R).identityK] using he

-- calibration lists for Tide.remove. In particular no enlargement(s) of Deck when mixing.
namespace Dictionary
open MS.Land MS.Menus MS.Rake
variable {B₁:MS.Local.Physical.Deck G}(D:Dictionary B₁) {i:ℕ}

def topic (g:Glyph B₁ i) (U:ℝ→T ℂ) : Letter G:= ⟨g.grade,D.cylinder g.size g.grade g.2.2,U⟩
def calibrated (D:Dictionary B₁)(a:Land.Prescription B₁)(u:Label B₁): Multiplet G :=
  (Finset.univ : Finset (Glyph B₁ u.h)).toList.map
    (fun i=> D.topic i (fun η k=> oil (a.fees u.h u.item) i k η))
omit [LinearOrder W] in
lemma equals_apply (a:Land.Prescription B₁)(u:W→Label B₁):
    reel a.team ∘ D.calibrated a ∘ u=Tide.ApplyM D.asLit (Stripped a.team) a u := by
  funext i; funext η; let Z:= u i
  change reel a.team (D.calibrated a Z) η= Menus.rent _ _ _ η
  unfold reel calibrated; rw [List.map_map, ← Multiset.sum_coe , ← Multiset.map_coe, Finset.coe_toList, ← Finset.sum];
  funext k; rw [Finset.sum_apply,Menus.rent]; refine Finset.sum_congr rfl fun g _=>?_
  simp_rw [Glyph.preamble, strip_wobble]; rfl
lemma applies (u:W→Label B₁) (a:Land.Prescription B₁)(t:Finset W): MS.Fleet.PhysicalSum G a.team y n true t c A (Tide.ApplyM D.asLit (Stripped a.team) a u)
    (exposed (n:=n) (landauPrimary h) a.team y A (t.toList.map fun w=>(c w,D.calibrated a (u w))) []) := by
  rw [← D.equals_apply]
  exact landau_physical h a.team y A _ _ t
end Dictionary
end YM.WilsonComparison.Finite
