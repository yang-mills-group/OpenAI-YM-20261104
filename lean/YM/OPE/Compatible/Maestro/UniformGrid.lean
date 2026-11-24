import YM.OPE.Compatible.Maestro.Garner
/-! Issued prognosis including all synchronized root moments and lifts for unsg. slot labels. No final phase estimates here. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float Next.Rank.Spindle Next.UVStress
open MeasureTheory
open scoped Topology Classical
open YM.OPE.Allot Series Pixel
variable {V:Type}[PartialOrder V][OrderBot V][Fintype V](D:Origin V) {Q:Finset V}
    {G:Gauge} {C:Family G}{F:Extraction.Order}{S:Table C.book}{η M:ℝ}
variable {I:Type}{l:Filter I}{T:I→ℝ}{s:I→V→ℝ}
set_option quotPrecheck false
variable (A:Allot C)(hC:C.Makes)(hG:G.Simple)(h: Glowing D Q l T s η)(hM:0 ≤ M) {b v W J K d:ℕ}
    (hI:Inward C F S)(p:brim D Q→ C.book.Token)
local notation "y"=> fun i=> schedule C b η (s i)
local notation "X"=> brim D Q
local notation "k"=> fun i=> scopeTick D C b v η (T i) (s i)
local notation "k'"=> fun i=> aperture D C b v η (T i) (s i)
local notation "R"=> fun i=> s i ⊥
local notation "d'"=> fun x:X=> (p x).1
local notation "D'"=> fun i=> volume D Q d' (s i)
local notation "j"=> fun i=> y i ⊥-1
-- accept v exponent, stamps arbitrary W≥
include h A hC hG hI hM
lemma issued (hJ:Stock.Tabs.opens C.path.levels 1 J K)(hT:C.ref d ≤ K)(hb:1 ≤ b):
    ∃ A' c₀:I→ℝ, Round l T (fun i=>A' i * D' i / R i^d) ∧ Round l T (fun i=>c₀ i * D' i / R i^d) ∧
     ∀ᶠ i in l, ∀ W:ℕ,∀ x:V→ Cover,Ridge (s i) η M D Q (C.S.gridPoint W ∘ x) →
       x ⊥=0 → (∀ a∈ allUp D Q,k' i a≤ W∧ ∃ z:Cover, C.S.gridPoint W (x a)= C.S.gridPoint (k' i a) z) →
       ∃ w:∀ a:X,C.label ((p a).fst), (∀ a:X, S.project _ (w a)=S.project _ ((p a).2)) ∧ ∃ q, Survival (C:=C) F J (j i) W (A' i) (c₀ i) (fun a:X=> ⟨(p a).1,w a⟩) (x∘Subtype.val) d q:=by
   obtain ⟨L,hL⟩:= exists_nat_ge (8*M/η+2)
   let f:ℕ→ℕ:= course C b L; have hK:= canopy_wave D hG A h b v J hM L hL
   obtain ⟨z,hz,hZ⟩:=fund D hG A h b v L; have hx(a:X) : a.val∈allUp D Q:= Finset.mem_union_right _ a.2
   have hg:=h.ray
   let w(i:I) :=scopeTick D C b v η (T i) (s i); have ht(x:X): Tendsto (fun i=> w i x.val) l atTop:= (climb D hG A h b v (v:=x.val) (hx x)).1
   let φ:= F.fuse
   obtain ⟨t',h'_⟩:= hI.crew d' (fun a:X=> (p a).2) (q:=fun (x:X) i=>k' i x.val) (l:=l) (fun x=> tendsto_atTop_mono (fun i=> Nat.le_succ (w i _)) (ht x))
   let a(i:I)(x:X):= fly C.path.levels ((p x).1) (k' i x.val) * C.S.a (k' i x.val)^((p x).1)/(2*β C (k' i x.val)^t' x)
   have hA(x:X): Round l T (fun i=> a i x/ s i (par D x.val)^(p x).1):=by
       let d'':=(p x).1
       obtain ⟨hK,hR⟩:= arrive D hG A h b v (v:=x.val) (hx _); let u i:= β C (k' i x.val)
       have he:Round l T (fun i=> fly C.path.levels d'' (k' i x.val)) := (hK.power (MergeProof.winter G d'') hg).inv
       refine ((he.mul (hR.power d'' hg)).div ((Round.const zero_lt_two hg).mul (hK.power (t' x) hg))).adjust ?_
       filter_upwards with i; unfold a; rw [div_pow]; ring
   let g(i:I):= CutOrder.grove D C Q (y i) (k i) (z i) (a i); let r i:= j i; let u' i:= rebate C (g i) d K (j i); let b' i:= owed C (g i) d (j i); let A' i:=2*(stakes C J K/u' i); let c' i:=2*b' i; obtain ⟨hQ,hV⟩:= all_pays D hG A h b v d' a d K hT hz hA
   have hp(x:X)(i:I):0<a i x:=by
       have hx:= β_pos C (k' i x.val); unfold a; rw [fly_eq]; have he:= C.S.a_pos (k' i x.val); positivity
   obtain ⟨hj,hJ',-⟩:= prev_info D hG A h b
   have hw:= lives D hG A h b h.crowned.base
   obtain ⟨u,hu⟩:= eventually_atTop.1 (A.bottoms.eventually_ge_atTop (places V)); refine ⟨A',c',?_,?_,?_⟩
   · refine ((Round.const (mul_pos zero_lt_two (show 0<stakes C J K from Real.exp_pos _)) hg).mul (Round.inv hV)).adjust ?_
     filter_upwards with i; change _*(u' i*_/_)⁻¹=_; unfold A'; simp_rw [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring
   · refine ((Round.const zero_lt_two hg).mul hQ).adjust (by filter_upwards with i; change 2*(b' i *_/_)=2*b' i*_/_; ring)
   filter_upwards [hj,hJ'.eventually_ge_atTop K,hJ'.eventually (Push.GridApprox.plenty C.path.levels J (lensScope C d)),hw.eventually_ge_atTop u,hK,hZ,h'_,(eventually_all.mpr fun i:X=> (ht i).eventually_ge_atTop (C.ref (d' i))),series_angle D hG A h b] with i hi hJ' hΩ hK hY hZ hV ht hs W x hx hy he
   obtain ⟨ψ,hψ,hU,g₀,h₀,hA⟩:= hV φ (by infer_instance) le_rfl
   refine ⟨g₀,h₀,?_⟩
   let p' (a:X): C.book.Token:= ⟨(p a).1,g₀ a⟩
   refine marvel D p' (a i) hG A hC hs (hY x W hx hy he) (fun i hi => hu i (hK.trans hi)) hJ hT hJ' hi hZ hb hΩ (fun a=> hp a _) (fun x=> ⟨ht x,rfl⟩) ψ hψ hU ?_
   filter_upwards [hA] with q hQ x; let e:= aperture D C b v η (T i) (s i) x.val; let t:=(p x).1; let r:= (C.S.a e)^t; let s':= fly C.path.levels t e
   have hc:0 < r:= pow_pos (C.S.a_pos _) _; have hV:0< s':= inv_pos.mpr (pow_pos (β_pos ..) _); let z:=Next.Rank.Spindle.paid C t e q.1 q.2 (g₀ x); let d'':=(β C e)^t' x; have hp:0< d'':=pow_pos (β_pos ..) _; have hh':z*r ≤ d'':=hQ x
   change 2*(s'*r/(2*d''))*z ≤ s'; field_simp; linarith only [hh']
end YM.OPE.Arboreal
