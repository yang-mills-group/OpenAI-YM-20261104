import YM.RegulatorIR.Cluster.Partial

/-! Removing the slot crop for Ito. Shapes T,V admit the broad kinetic
bounds `Brief`, costs through the coefficients actually entering the identity
(finite). -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Finset Function Budget Budget.Packet Budget.Layer Budget.Tuple Diagram Filter
open scoped Topology BigOperators Classical ENNReal
variable {X Y:Type}{r s k e p:ℕ}

def Last (T:Y→Rhythm X)(U: Rhythm X)(v:Filter Y)(p:ℕ) : Prop:=∀ i e,e≤p→∀ r,Tendsto (fun l=>T l i e r) v (𝓝 (U i e r))
lemma draws_sym {T:Y→Packet X r}{U:Packet X r}{v:Filter Y}(h:Tendsto T v (𝓝 U)): Tendsto (fun l=>symmetry (T l)) v (𝓝 (symmetry U)):=by
 apply tendsto_pi_nhds.mpr;intro z; simp_rw [symmetry_at]; exact Tendsto.mul tendsto_const_nhds (tendsto_finsetSum _ (fun _ _=> tendsto_pi_nhds.mp h _))
lemma draws_scale {T:Y→Packet X r}{U:Packet X r}{v:Filter Y}(h:Tendsto T v (𝓝 U))(t:ℝ): Tendsto (fun l=>t • T l) v (𝓝 (t • U)):=tendsto_const_nhds.smul h
lemma lasts {T S:Y→Rhythm X}{U Q:Rhythm X}{v:Filter Y}(h:Last T U v p)(hh:Last S Q v p) : Last (fun w=>composeT (T w) (S w)) (composeT U Q) v p:=by
 intro i e he r; unfold composeT accord crisp
 apply tendsto_finsetSum;intro a _;apply tendsto_finsetSum;intro b hb; apply tendsto_finsetSum; intro c hc
 rw [← mem_antidiagonal.mp hc];simp only [pie];apply draws_sym; apply tendsto_pi_nhds.mpr; intro x
 have hx:= mem_antidiagonal.mp hb; exact (tendsto_pi_nhds.mp (h a.1 b.1 (by omega) c.1) (cutLeft x)).mul (tendsto_pi_nhds.mp (hh a.2 b.2 (by omega) c.2) (cutRight x))

def Price (T:Rhythm X)(p:ℕ) : Prop:= ∀ k e,e≤p → ∀ r, quota (T k e r) 1≠⊤
def Cost (T:Rhythm X)(p:ℕ) : Prop:=∀ k e,e≤p → ∀ r,Enough (T k e (r+1))
lemma price_cost {T:Rhythm X}(h:Price T p):Cost T p:=fun k e he r=>enough _ (h k e he (r+1))
lemma presume (T:Packet X r)(U:Packet X s)(h:quota T 1≠⊤)(hh:quota U 1≠⊤): quota (joined T U) 1≠⊤:=by
 let A:Tariff X:= {road:=fun _ _=>1, unit:=fun _ _=>le_rfl,own:=fun _=>rfl, symm:= fun _ _=>rfl, tri:= fun _ _ _=>by simp }
 let B:=Premium.free A
 apply ne_top_of_le_ne_top (by finiteness) (le_trans (le_trans (quota_mono (joined T U) (u:=B.width) (w:=1) (fun x=>B.width_unit x)) (mark_symmetry (T:=untied T U))) (le_of_eq (show markQ B (untied T U) = quota T 1*quota U 1 from ?_)))
 have ht : ∀ n,B.width (r:=r+s) n=1 := fun n=> le_antisymm (B.width_le (A.diameter_le le_rfl (fun _ _=> le_rfl)) (fun _=>le_rfl)) (B.width_unit n)
 unfold markQ quota
 simp_rw [ht,mul_one,Pi.one_apply,mul_one]
 rw [← (Fin.appendEquiv ..).tsum_eq, ENNReal.tsum_prod']; simp_rw [show ∀ p:Tuple X r × Tuple X s,untied T U ((Fin.appendEquiv ..) p) = T p.1 * U p.2 from fun p=>by change untied _ _ (Fin.append p.1 p.2)=_;simp [untied], enorm_mul]; rw [← ENNReal.tsum_mul_right]; apply tsum_congr; intro x; exact ENNReal.tsum_mul_left
lemma packable {Y:Type} (S:Finset Y)(T:Y→Packet X r)(h:∀ i∈S,quota (T i) 1≠⊤):quota (∑ i∈S,T i) 1≠⊤:= ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr h) (quota_sum ..)
lemma price_product (T S:Rhythm X)(h:Price T p)(hh:Price S p): Price (composeT T S) p:=by
 intro i e he r;unfold composeT accord crisp; apply packable; intro a _; apply packable; intro b hb; apply packable; intro c hc
 rw [← mem_antidiagonal.mp hc]; simp only [pie]; have ht:= mem_antidiagonal.mp hb; exact presume _ _ (h a.1 b.1 (by omega) _) (hh a.2 b.2 (by omega) _)

variable {K:Layer X X}{M:Tariff X}{t:ℝ≥0∞} {V T U : Rhythm X} (hV:Cost V p)(ht:Price T p)(hb:row K M id id t)(hv:t ≠ ⊤)
include ht hb hv
lemma convection : Last (fun l k e=> heating (pall K l) (T k e)) (fun k e=> heating K (T k e)) atTop p:=fun k e he _=> draws_scale (draws_sym (tendsto_pi_nhds.mpr (fun z=> loop_winds _ _ z (ht k e he _) (row_to_sup hb) hv))) _
include hV
lemma volley : Last (fun l=>drift (pall K l) T V) (drift K T V) atTop p:=by
 intro k e he r; unfold drift carry force; apply tendsto_finsetSum; intro a _; apply tendsto_finsetSum; intro b hh; apply tendsto_finsetSum; intro c hc
 rw [← mem_antidiagonal.mp hc]; simp only [matchTwo]
 have hx:= mem_antidiagonal.mp hh; exact draws_scale (draws_sym (tendsto_pi_nhds.mpr (fun z=> knot_winds (T a.1 b.1 _) (V a.2 b.2 _) (ht a.1 b.1 (by omega) (c.1+1)) (hV a.2 b.2 (by omega) c.2) hb hv z))) _
lemma flocks : Last (fun l=>Root T V (pall K l)) (Root T V K) atTop p := fun i e he r=>(convection ht hb hv i e he r).add (volley hV ht hb hv i e he r)

lemma Ito_atom {a b c:ℕ}(A: Brief a T)(B:Brief b U)(C:Brief c V)(hu:Price U p)(hs : ∀ i j,K i j= K j i)(k e:ℕ)(he:e≤p): Root (composeT T U) V K k e = composeT (Root T V K) U k e+composeT T (Root U V K) k e +drift K T U k e:=by
 ext1 r
 have h₁:=flocks hV (price_product T U ht hu) hb hv k e he r
 have h₂ (V:Rhythm X) : Last (fun _:Finset X=>V) V atTop p:=fun _ _ _ _=> tendsto_const_nhds
 have h₃:= Tendsto.add ((lasts (flocks hV ht hb hv) (h₂ U) k e he r).add (lasts (h₂ T) (flocks hV hu hb hv) k e he r)) (volley (price_cost hu) ht hb hv k e he r)
 change _=composeT (Root T V K) U k e r+composeT T (Root U V K) k e r+drift K T U k e r; apply tendsto_nhds_unique h₁; convert h₃ using 1; ext1 l
 have HH: Brief.Limited (Brief.tile l) (pall K l):=by
    intro x y h; have h': x∈l ∧ y∈l:=by unfold pall at h;split at h; assumption; contradiction
    exact ⟨⟨⟨x,h'.1⟩,rfl⟩,⟨⟨y,h'.2⟩,rfl⟩⟩
 exact congr_fun (congr_fun (congr_fun (Brief.partialK A B C l (K:=pall K l) (fun i j=>by simp only [pall, hs i j]; by_cases h:i ∈ l <;> simp [h]) HH) k) e) r
end YM.RegulatorIR.Cluster
