import YM.MS.Fleet.Fold
import YM.MS.Vista.Rope

/-!
Index sets independent of reciprocal mesh. The mark centers are *offsets from a common anchor
x*. `voyage` converts mixed marked vertices from based to addressed (root at min) and sets
R = exp(t). Quantitative: compare coefficients at the same actual offsets; no approximate
replacement of positions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W]{L:I→Side}{S:Finset W}
 {F H:Glade G I}{X:Rake.Dance G I W}{K:Latch.Edge G}

abbrev Berth := W→ Faces I
variable (c:Berth ( W:=W ) ( I:=I )) (A:Faces I)
def anchorC (S:Finset W): Faces I:= if h:S.Nonempty then c (S.min' h) else 0
abbrev info (c:Berth ( W:=W ) ( I:=I )) : Position W I:= fun x=> Tone.embed ∘ c x
local notation "δX"=>rootX (info c)
local notation "Ψ"=> ( outside L )
local notation "m0"=>fun (_:I)=>planeF
open Rake.Geo
local notation "ρk"=> ( constantP G I (LowP G) )
local notation "Y"=> ( constantP G I (PlanetL G) )
local notation "ιW"=> ( Orbit.uniform G I )
lemma Vroot (S:Finset W)(i:I): δX S i= Tone.embed ( anchorC c S i ):= by unfold rootX anchorC; split; rfl; ext; simp [Tone.embed]
lemma T_root {t:Finset W}(h:t∈ picks S): anchorC c S= anchorC c (S\ t):= by
    funext i x; obtain ht:= congr_fun ( congr_fun ( unfT ( info c ) h ) i ) x; rw [ Vroot,Vroot ] at ht; unfold Tone.embed at ht; exact_mod_cast ht
omit [LinearOrder W] in
abbrev unload (A:Cover) (F:Law G) : Law G := sleeve weightψ ( lodging (-A) F ) -- no dependence on W
lemma accountable (A:Cover)(X:Law G): lodging A ( sleeve lace (unload A X) )= X:= pack_home A -- unused W inferred
abbrev vessel (F:Glade G I)(x:I→ Cover) : Glade G I:= fun i t=> unload (x i) ( F i ( exp t ) )
def voyage (X:Rake.Dance G I W): Rake.Dance G I W:= fun p n=> vessel ( X p n ) ( anchorC c p )
-- removing extra half or direct or mesh. first transform $mode`
abbrev frameL (A:Cover): Op (Lane4 G) ℂ:= (lodging A).comp ( sleeve lace )
lemma f_l (A:Cover)(t:Law G): frameL A t=lodging A (sleeve lace t):= rfl
lemma f_inj (A:Cover): Injective (frameL A ( G:=G )):= fun a _ h=> ( unpack_home A ( F:=a ) ).symm.trans ( Eq.trans (congr_arg ( unload A ) h ) (unpack_home A) )
variable {B:Local.Physical.Deck G}
open Land Program
variable (T:Prescription B){i:I}{n:ℕ}{R: Rake.Geo I}{t:ℝ}{x:Cover}
local notation "πA"=> Scope G (Wind.skyline G T.team) R.η
omit c in -- not included. omit marker W maybe unused.
lemma τuis (hu:Toned F) (v:Faces I) (P':Faces I)(i:I)(t:ℝ) : frameL (v i) ( G:=G ) ( sailP (m0) Y (vessel F v) i t )= (exp t:ℂ) • zip0 Ψ ιW P' F i ( exp t ):= by
   let X:=vessel F v i t; let K:= Cpu G (exp t); let A:=v i; let P:=LaceL G (exp t); let c:ℂ:= exp t; have hf : lodging A ( sleeve lace X )= F i (exp t):= accountable ..
   rw [ flat_zip0 Ψ rfl ]; change frameL A (cycle (PlanetL G t) planeF X)=c • Θ_pc false μzone 0 P (F i (exp t)); rw [PlanetL,scaleL,spread_s, cycle_fee]; -- inspect
   rw [f_l,map_smul (sleeve lace), map_smul ( lodging A ), ← skin_c,← be_cycle, ← spread_d,hf,tr_town hu,Θ_z]; -- order of rw
lemma berth_b (p:Faces I)(u:ℕ)(i:I)(t:ℝ):
  frameL (p i) (expJ ρk (initials R T u) (vessel F p) i t)=
       (exp t:ℂ) • expJ ιW (πA u) F i (exp t):= by
   let S:=Cpu G (exp t); let A:=p i; let h0:=vessel F p i t; let f:= Wind.skyline G T.team u (R.η i) (exp t); change frameL A ( tree parity ( LowP G t ) f h0 )= _ • tree parity ( dope S ) (sleeve lace f) _; rw [scaleL,Wind.lineT, map_smul, f_l, ← D_tree ( Vrev G (exp t)),← be_tree A ( Dk_rev (Vrev G (exp t)) ), show lodging A (sleeve lace h0)=F i (exp t) from accountable ..]
lemma lights (v:I→Cover) (n:ℕ)(i:I)(t:ℝ) (U:Rake.Site G I): frameL (v i) ( lonely ρk (initials R T) (fun k=> vessel ( U k ) v) n i t )=(exp t:ℂ) • lonely ιW πA U n i ( exp t ):= by
   unfold lonely; simp_rw [Finset.sum_apply,Finset.smul_sum,map_sum]; exact Finset.sum_congr rfl fun j hj=> berth_b T v _ i t
lemma voyage_root (p:Finset W)(h:p∈ picks S): voyage c X ( S \ p ) n=vessel ( X ( S\p ) n ) ( anchorC c S ) := by rw [ T_root c h ]; rfl -- rw changes all S occurrences.
lemma π_joins (p:Finset W)(h:p∈ picks S) (i:I)(t:ℝ)(j k:ℕ)
       (T':Toned (X p j))(U': Toned ( X (S\p) k )):
    frameL ( anchorC c S i ) ( regionC (m0) (δX p-δX S) Y (voyage c X p j) (voyage c X (S\p) k) i t )=( exp t:ℂ ) • ( zip2 Ψ ιW A A ( X p j ) ( X ( S\p ) k ) i (exp t) ):= by
   let v:= anchorC c p; let z:=anchorC c S; let S0:=X p j; let P0:= X (S\p) k; let t₀:= exp t; let F:= vessel S0 v i t; let D:= vessel P0 z i t; have he : (δX p-δX S) i= Tone.embed ( v i-z i ):= by rw [emb_sub,Pi.sub_apply,Vroot,Vroot] -- Pi.sub order
   rw [voyage_root c p h, zip2, show adjust (Ψ).orbit ( feeling Ψ true A A ιW S0 P0 )=( 0: Glade G I ) from rfl,add_zero]; unfold feeling; rw [sub_self,show Dph false (A i) (A i)=0 from ( by simp [Dph,taste] ) ]; change frameL ( z i ) ( Cabin _ ( PlanetL G t ) _ F D ) = (exp t:ℂ) • PairV false μzone 0 0 (LaceL G t₀) ( S0 i t₀ ) ( P0 i t₀ ); rw [ he, ← frameV, PlanetL,scaleL,spread_s,Vista.pair_fee,map_smul, f_l, ← Dcrew, ← joint ( v i ) ( z i ), show lodging ( v i ) ( sleeve lace F )=S0 i t₀ from accountable .., show lodging ( z i ) ( sleeve lace D )=P0 i t₀ from accountable .., ← spread_d ]; exact congr_arg ((exp t:ℂ) • · ) ( join_town 0 T' U' i _ )

end YM.MS.Fleet
