import YM.RegulatorIR.Axial.Drapes

/-!
# W1 beyond θ for compact rays (rotation or gauge)
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight PowerSeries Gain Prim Motion Budget.Packet Budget.Deck
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{W:Type}{M:W→ℕ}{n:Page M→Side}{S:Heir n G} (H:Reel S)(T:S.Accounts) (V:H.Follows T)(w:W) (hh:Common H)
variable {p j e k:ℕ}{L:Meter W} (A:S.Supplies T L p k)(B:Aug.Amenities S L p k)
local notation "E" => eternal H w
local notation "R" => grove H w hh
local notation "F" => tele H T w
variable (i:ℕ)(h:i ≤ M w)
variable (hp:14≤k)
variable (ht:Layer.Sym (S.maps (Page.mk w i h)) (S.maps (Page.mk w i h)) (H.stem (Page.mk w i h)))(hR:Billed (H.stem (Page.mk w i h)))
variable {r s:Signed}{x y:(z:Side)→ℝ→ Horizon G (big w n (Aug.sheet w i h z))}
variable {a:Foot G→ℝ⟦X⟧}
local notation "v" => Page.mk w i h
variable (D:Brief r (n (Page.mk w i h)) x a)
include hh V A D ht hR
omit V in
lemma readsO (hf:e ≤ p): Tendsto (fun z=> let u:= Aug.sheet w i h z; coeff e (money ((R).stance u) (haloT F u) (x z))) atTop
 (𝓝 (profitX (H.stem (Page.mk w i h)) (T.bulk (Page.mk w i h)) a e)):=by
 let K:= H.stem v;let U:= T.bulk v
 have hy: (T).bulk v=U:=rfl
 let f:= n v; let c:= H.even v; let P:= S.P w; let hn:S.l v*(n v).val=P:= H.phase v; let Q(z):= playS (G:=G) (Sight.slab z) c hn
 rw [profit_sum _ _ (T.cap_b (fun i=> essential H i) v)]
 have hq: Layer.Sym (Carto G _ P c hn) (Carto G _ P c hn) K:=by rw [← H.realms];exact ht
 let g(z:Side) := haloT (F) (Aug.sheet w i h z)
 let f' z:=vow (peel (x z))
 let y z:= (R).stance (Aug.sheet w i h z)
 have hl : Tendsto (fun z=> coeff e (tale (steam (y z) ∘ (x z)))) atTop (𝓝 (rhyme a (coil K) e)):=by
    have hf : Tendsto (fun z=> rhyme (f' z) ((Q z).deckSum (coil K)) e) atTop (𝓝 (rhyme a (coil K) e)):= Brief.owns D c hn (H.deep v) (coil_r _ K hq) 0 (coil_f _ hR)
    apply hf.congr'; filter_upwards [D.sky] with z hz
    let u:= Aug.sheet w i h z; refine Eq.trans ?_ (jetInk ((R).stance u) (x z) hz)
    have hr: Layer.Sym (Q z) (Q z) K:=by intro d x y; unfold Q; rw [Halo.steering,Halo.steering]; exact hq ..
    apply congr_arg (fun t=> rhyme (f' z) t e); exact funext (deck_costA (Q z) K hr)
 have hp : Tendsto (fun z=> coeff e (reel (g z) 2 (x z))) atTop (𝓝 (rhymeR a (pulp U) 2 e)):=by
    simp_rw [rhyme_tube]; unfold rhymeR; refine tendsto_finsetSum _ fun j hj=> tendsto_finsetSum _ fun d _=>?_
    by_cases he:d=0
    · subst d; let b:= pulp U j.1 0
      have ht(z):g z j.1 0=0:=by unfold g haloT;ext1 u; rw [deckSum,dif_neg (by omega)]; rfl
      simp [ht,pulp, rhyme]
    rw [pulp,if_neg he]; have hl:j.1≤p:=by have hx:= Finset.mem_antidiagonal.mp hj;omega
    obtain ⟨b,hB,hH⟩:= A.bulk_price j.1 hl d
    have hD(i':Fin d)(w':Foot G): Summable (fun p:Hold i' w'=> T.bulk v j.1 d p.val):= quota_summable (fun p=> (S.census.cone k v).diameter_unit p.val) (ne_top_of_le_ne_top (hB.cost v) (hH v i' w'))
    have hb:= A.bulk_deck v j.1 d hl;rw [H.realms] at hb; exact Brief.owns D c hn (H.deep v) hb ⟨0,by omega⟩ (fun x=> (hD ⟨0,by omega⟩ x).norm)
 change Tendsto (fun z=> coeff e (tale _ + _)) _ _
 simpa only [map_add] using (show Tendsto (fun z=> coeff e (tale (steam (y z) ∘ x z)) + coeff e (reel (g z) 2 (x z))) _ _ from hl.add hp) -- rewrite wrong
include B hp
lemma values {b:Foot G→ℝ⟦X⟧}(Y:Brief s (n (Page.mk w i h)) y b) (he:e≤p)(hxy: ∀ᶠ z:Side in atTop,reel_prop (x z) (y z) ∨ ∃ q,ribbon q (x z) (y z)) : profitX (H.stem v) (T.bulk v) a e=profitX (H.stem v) (T.bulk v) b e:= by
 have h:=readsO H T w hh A i h ht hR D he; have h':=readsO H T w hh A i (show i ≤ M w from by assumption) ht hR Y he
 apply tendsto_nhds_unique (h.congr' ?_) h'; filter_upwards [D.sky,Y.sky,hxy] with z hz hy ha; exact deeper H T V w hh A B i (show i ≤ M w from by assumption) hp ht hR z (x z) (y z) hz hy ha e he
end YM.RegulatorIR.Axial
