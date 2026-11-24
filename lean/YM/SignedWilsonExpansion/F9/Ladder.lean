import YM.SignedWilsonExpansion.F9.Pier

/-!
# In the same nodal booth lower ranks retain their owner-height projections
Concretely use the actual `Labels.frames` coherent lifts. This isn't the
signed/MS change of fields and doesn't take a new representation at each
geometry demand. Like `OPE.Gradient.Lift.frame_range`, this records tower
rank inclusions without engineering variation across the letter. Prove row
compatibility directly at all orders for the offshell ranks receiving the
reports. No station identities of physical quotient asserted here.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h p k m c N u e i j l r n d q:ℕ}{F:Labels.Frame G h}{H:Hol G}
variable {B M X Y z:ℝ}{P:Era G ℝ}
section
variable (U:Labels.Frames G)
lemma climb_exists (h:d≤k)(i:(U.level d).Index) : ∃ x, (U.level k).basis x=raiseLabel G h ((U.level d).basis i):=by
    induction k,h using Nat.le_induction with
    | base=> exact ⟨i,rfl⟩
    | succ d h ih=>
       obtain ⟨j,hj⟩:= ih; have hp:= U.coherent d (show raiseLabel G d.le_succ ((U.level d).basis j)∈ Set.range (raiseLabel G d.le_succ ∘ (U.level d).basis) from ⟨j,rfl⟩); rw [hj] at hp; exact hp
def upL (h:d≤k) (i:(U.level d).Index) := (climb_exists U h i).choose
lemma climb (h:d≤k) (i:(U.level d).Index): (U.level k).basis (upL U h i)=raiseLabel G h ((U.level d).basis i):=(climb_exists U h i).choose_spec
lemma up_grade (h:d≤ k)(i:(U.level d).Index): (U.level k).grades (upL U h i)=(U.level d).grades i:=pure_unique ((U.level k).basis.ne_zero _) _ _ ((U.level k).pure _) (climb U h i ▸ (show raiseLabel G h ((U.level d).basis i) ∈ Grade _ from (U.level d).pure i))
lemma up_faith (h:d≤ k): Injective (upL U h):=fun i j t=>(U.level d).basis.injective (Submodule.inclusion_injective _ (show raiseLabel G h ((U.level d).basis i)= _ from (climb U h i).symm.trans ((congr_arg ((U.level k).basis) t).trans (climb U h j))))
def upT (h:d≤k)(i:TagIx (U.level d) r): TagIx (U.level k) r:=⟨upL U h i.val,up_grade U h i.val▸ i.property⟩
lemma up_w (h:d≤k)(i:TagIx (U.level d) r): wT (U.level k) (upT U h i)= wT (U.level d) i:= congr_arg Prod.fst (up_grade U h _)
lemma up_trans (h:d≤l)(v:l≤k)(i:(U.level d).Index): upL U v (upL U h i)=upL U (h.trans v) i:= by apply (U.level k).basis.injective; rw [climb,climb,climb]; rfl
lemma upT_faith (h:d≤k)(i j:TagIx (U.level d) r)(q:upT U h i=upT U h j): i=j:=Subtype.ext (up_faith U h (congr_arg Subtype.val q))

lemma price_weight (x : Label G k)(e:x∈Grade (n,l))(h:n≤d):x.val∈localFields G d:=by
    refine ⟨(MvPolynomial.mem_restrictSupport_iff ℂ).mpr (fun j hj => ?_),x.property.2⟩
    have he:= ((pure_grade _ _).mp e) (MvPolynomial.mem_support_iff.mp hj); rw [weight_slot] at he; exact (show height j = n from congr_arg Prod.fst he).trans_le h

-- every handover through weight d, exactly onto its label
lemma descent (u:d≤ k)(i: (U.level k).Index)(w:((U.level k).grades i).1≤d): ∃ j,upL U u j=i:=by
    let Q:= U.level k; let H:=U.level d; let v:= Q.basis i; have Hv:= Q.pure i; have hv:v.val∈localFields G d:= price_weight v Hv w; let s : Label G d:= ⟨v.val,hv⟩
    by_contra! g; have he: v= raiseLabel G u s:= rfl; have ht: Q.coords (raiseLabel G u s) i=0:=by
       rw [← H.basis.sum_repr s,map_sum,map_sum,Finset.sum_apply]; apply Finset.sum_eq_zero; intro b _; unfold Q H; rw [map_smul,map_smul,Pi.smul_apply,← climb U u b,Frame.coords_basis,Pi.single_eq_of_ne (show i ≠ _ from Ne.symm (g b)),smul_zero]
    rw [← he,show Q.coords v= Pi.single i 1 from Frame.coords_basis Q i,Pi.single_eq_same] at ht; exact one_ne_zero ht
abbrev downL (u:d≤k)(i:(U.level k).Index)(w:((U.level k).grades i).1≤d): (U.level d).Index:= (descent U u i w).choose
lemma up_down (u:d≤k)(i:(U.level k).Index)(w: ((U.level k).grades i).1 ≤ d): upL U u (downL U u i w)=i:= (descent U u i w).choose_spec
lemma down_grade (u:d≤k)(i:(U.level k).Index)(w: ((U.level k).grades i).1 ≤ d): (U.level d).grades (downL U u i w)=(U.level k).grades i:= (up_grade U u _).symm.trans (congr_arg _ (up_down U u i w))
def downT (u:d≤k)(i:TagIx (U.level k) r)(h:wT (U.level k) i≤d): TagIx (U.level d) r:= ⟨downL U u i h,(by rw [down_grade]; exact i.property)⟩
lemma up_downT (u:d≤k)(i:TagIx (U.level k) r)(h:wT (U.level k) i≤d): upT U u (downT U u i h)=i:= Subtype.ext (up_down U u i.val h)
lemma fare_up (h:d≤k)(i:(U.level d).Index)(v:Label G d): (U.level k).coords (raiseLabel G h v) (upL U h i)= (U.level d).coords v i:= by
    rw [← (U.level d).basis.sum_repr v]; simp_rw [map_sum, map_smul,Finset.sum_apply, Pi.smul_apply,←climb U h, Frame.coords_basis]; simp [Pi.single_apply, (up_faith U h).eq_iff]
end

lemma engineered_expand (J:Jet G)(t:ℝ)(h:ℕ): expand h (engineered t (trunk h J))= scaleJet (expand h (trunk h J)) t:=by
    funext i; simp only [expand,scaleJet]; split; rfl; rw [smul_zero]
lemma moveExpand (h:d≤k)(J:Snap G d)(t:ℝ): expand k (engineered t (trunk k (expand d J)))=expand d (engineered t J):=by
    have hp: expand k (trunk k (expand d J))= expand d J:=by
       funext i; by_cases v:i<k-1; · simp only [expand,dif_pos v,trunk]
       have ho:¬i<d-1:=by omega
       simp [expand,v,ho]
    nth_rw 2 [← trunks J]; rw [engineered_expand,engineered_expand,hp,trunks]
lemma grain_access (d:ℕ)(X:Snap G d)(i:YForest G): grain X i=access X (feather i) i.2.2:=by
    unfold grain sampled; obtain ⟨a,j,rfl⟩:=every_stone i; rw [feather_at]; change steady (road (Place.seat a.1) a.2 X) j= _; rw [steady_eq,funext (represented_signal a X)]; rfl

lemma in_horizon (h:d≤k)(J:Snap G d)(q:ℝ)(i:YForest G): grain (engineered q (trunk k (expand d J))) i= grain (engineered q J) i:=by
    rw [grain_access,grain_access]; apply congrArg (fun c:G.Color=> c i.2.2); unfold access; apply congr_arg (fun f:ℝ→G.Color=>∫ s:ℝ in 0..1,f s) ?_; funext s
    simp only [partConnection,one_smul,Source.potential,moveExpand h]
    refine (Finset.sum_subset (Finset.range_mono (by omega)) ?_).symm; intro i p t
    have hv: ¬ i<d-1:=fun v=>t (Finset.mem_range.mpr v); rw [expand,dif_neg hv]; rfl

def vitre (h:ℕ)(F:ChamberTen G ℝ r): Glas G h r:= arret (page (h+1) (testa (h+1) 0)) (wire (h+1) ∘ F) h r
lemma sheen (u:Fin r→ YForest G)(J:Snap G h): Tensor.diagonal (latent (skyline h u r)) J=∏ i, grain J (u i):= on_k u J
lemma vineyard (h:ℕ)(J:Jet G)(x:ℝ)(u:Auth k P):
    Fountain.vein (vitre h (P.2 e r)) J x= ∑' v:Fin r→YForest G, (P.2 e r v)*(∏ i, grain (engineered x (trunk h J)) (v i)):=by
    obtain ⟨s,t,hs,ht⟩:= ((u.tuft (wire (h+1))).wing e r).land; unfold Fountain.vein vitre; rw [lat_sum _ _ _ _ (show Twig 0 s t (wire (h+1) ∘ (P.2 e r)) from ht) hs] -- replace
    apply tsum_congr; intro i; rw [Function.comp_apply,wire_apply,_root_.smul_apply,eye_wall,if_pos rfl,sheen,smul_eq_mul,mul_one]
lemma fundedSeed (H:Hol G)(u:Auth k P)(t:l≤h): seedTile (vitre h (P.2 e r)) l ∈ localFields G h:=by
    obtain ⟨s,v,hs,ht⟩:= ((u.tuft (wire (h+1))).wing e r).land; exact seed_paint H _ ht hs ((stakes P u _).m e r) _ _ t
lemma seed_horizon (H:Hol G)(u:Auth k P)(p:l≤h)(v:h≤d): seedTile (vitre h (P.2 e r)) l= seedTile (vitre d (P.2 e r)) l:=by
    let T:=P.2 e r; let a:=seedTile (vitre h T) l; let b:=seedTile (vitre d T) l; let X:Label G h:= ⟨a,fundedSeed H u p⟩; let Y': Label G d:=⟨b,fundedSeed H u (p.trans v)⟩; let Y: Label G h:= ⟨b,price_weight Y' (n:=l) (l:=r) (seed_grade ..) p⟩
    apply Labels.eval_ext; intro J; let V:=expand h (trunk h J); rw [← show Labels.read V X.val=_ from racts X J, ← show Labels.read V Y.val=_ from racts Y J];
    change Labels.read V a = Labels.read V b; unfold a b; rw [reads_seedTile,reads_seedTile]; congr 2; funext x; unfold T; rw [vineyard _ _ x u,vineyard _ _ x u]; unfold V; simp_rw [trunks, in_horizon v]
lemma seed_row (H:Hol G)(u:Auth k P)(i:TagIx F r): row F (P.2 e r) i= ((F.coords (⟨seedTile (vitre h (P.2 e r)) (wT F i),fundedSeed H u (F.bound _)⟩:Label G h)) i).re:=by
    unfold row echoS trellis; rw [show valence F (Xa.seat ..)= r from i.property]; exact congr_arg (fun c:F.Coeff=>(c i).re) (detecting _ _ _ (fundedSeed H u (r:=r) (F.bound i.val)))
lemma row_handed (H:Hol G)(U:Frames G)(u:Auth k P)(i:TagIx (U.level h) r)(v:h≤d): row (U.level h) (P.2 e r) i=row (U.level d) (P.2 e r) (upT U v i):= by
    let F:= U.level h; let w:= wT F i; let x: Label G h:= ⟨seedTile (vitre h (P.2 e r)) w,fundedSeed H u (F.bound i.val)⟩; rw [seed_row H u i, ← fare_up U v i x,seed_row H u (upT U v i)]; apply congr_arg Complex.re; apply congr_arg (fun c:Label G d=>(U.level d).coords c (upT U v i)); apply Subtype.ext; change _ = seedTile _ _; rw [up_w]; exact seed_horizon H u (F.bound _) v
end YM.WilsonCoeffUV.Mer.Xa
