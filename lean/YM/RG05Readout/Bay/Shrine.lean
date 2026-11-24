import YM.RG05Readout.Bay.Masthead
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Bay
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l:ℕ}(h:C.Makes)
set_option quotPrecheck false
open Extraction
local notation "α!"=> C.S.a
open Metric
open Poem
local notation "T"=> (Cells.center)
local notation "U"=> C.S.toDepth
-- meter permits ANY margin offset within 1/16 of center.Relative.
variable {u:Cover}
local notation "G'"=> C.S.gridPoint
local notation "κ"=> Lattice.wrap
section
variable (ht:j ≤ N)
local notation "V'"=> T C.S p ht 0
lemma inside0 (x : Site (C.side N p))(hs:separation x 0≤ (C.S.toDepth ht p).count.val/16) : x∈(V'|>.margin 0 ((C.S.toDepth ht p).count.val/8)):=by
    let D:= (U ht p); let T':=(V'); let l:=D.count.val; let d':=l/2; let w:= l/8; have hL : 0 < l:= D.count.property; have hv:separation x 0≤ l/16:=hs
    have ht(a:Axis): let t:=T'.coordinated 0 x a; t<l ∧ w ≤ t ∧ t+w+1 ≤l :=by
       intro z; let s:= lift x a; have he:s.natAbs ≤ l/16:=by rw [separation,sub_zero] at hv; exact (component_le x a).trans hv
       let b:ℤ:= d'+s; have hb:0≤b:=by unfold b d'; omega
       have hl:b.toNat<l:=by unfold b d' at *; omega
       have hQ:T'.starts 0 a=0-(d':Per (C.side N p)):=by rw [Tiling.starts_zero]; rfl
       have hZ: x a-T'.starts 0 a= (↑b.toNat:Per (C.side N p)):=by
          rw [hQ,←Int.cast_natCast (R:=Per (C.side N p)) b.toNat,Int.toNat_of_nonneg hb, show x a= (s:Per _) from (congr_fun (wrap_lift x) a).symm]; unfold b; push_cast; abel
       have Hz:z=b.toNat:=by unfold z Tiling.coordinated; rw [hZ,ZMod.val_natCast_of_lt (hl.trans T'.narrow)];
       unfold b d' w at *; omega
    exact ⟨fun i=> (ht i).1,fun i=> (ht i).2⟩
-- Size via exact serialization on mesh b. All p large permit primitive u in cover.
lemma mesh_fit {x:Site (C.side N p)}(hh:dist (C.S.place x) (C.S.gridPoint j u)≤ α! j/16): separation x ((U ht p).embed (κ _ u)) ≤ (U ht p).count.val/16:=by
   let T':=(U ht p); let v:=(κ (C.side j p) u); let a:= x-(T'.embed v); let s:= T'.count.val; let z:Cover:= lift x - s • u
   have he:Lattice.wrap (C.side N p) z=a:=by unfold z a; rw [map_sub,Lattice.wrap_lift]; rw [T'.embed_wrap]
   have hz:G' N z=C.S.place x-(G' j u) :=by
      apply PiLp.ext; intro i
      change (α! N)*(((lift x i:ℤ) - s • u i:ℤ):ℝ)=(α! N)* ((lift x i:ℤ):ℝ)- (α! j)*(u i:ℝ)
      rw [nsmul_eq_mul]; push_cast; rw [← C.S.embeds_scale T']; ring
   obtain ⟨hx,hσ⟩:= Harvest.radius_paid C j p; have h₀:‖G' N z‖ ≤ (α! j)/16:= by rw [hz,← dist_eq_norm]; exact hh
   have hR: lift a=z:= reads_grid he (by linarith only [h₀,hx,hσ]); have hA:= (Ribbons.normC C N p a).1
   rw [Schedule.place,hR] at hA; have ht: separation x (T'.embed v)=separation a 0:=by unfold separation; rw [sub_zero]
   have he': 16*separation a 0≤ s:=by
       have hX: α! N*s=α! j:= C.S.embeds_scale _
       exact_mod_cast le_of_mul_le_mul_left (show α! N*(16*(separation a 0:ℝ)) ≤ α! N*s from by linarith only [hX,hA,h₀]) (C.S.a_pos _)
   rw [ht]; change separation a 0 ≤ s/16; omega

lemma serial (x i:Site (C.side N p))(v: Site (C.side j p))(hv:(V'|>.copyMap v i)=x) : separation x ((U ht p).embed v)=separation i 0 :=by
    rw [← hv,show (U ht p).embed v=(V'|>.copyMap v 0) from ((copy_home ..).trans (zero_add _)).symm]; unfold Tiling.copyMap affine; rw [separation_translate,separation_signed]
lemma margin_fit {x:Site (C.side N p)}(hp:dist (C.S.place x) (G' j u)≤ (α! j)/16) : x∈ (V'|>.margin (κ (C.side j p) u) ((V'|>.side.val)/8)):=by
    let v:=κ (C.side j p) u; obtain ⟨z,h⟩:= (V'|>.pointed v x); rw [←h,← Cells.Tiling.reflected_margin]; exact inside0 ht z ((serial ht x z v h).symm ▸ mesh_fit ht hp)
local notation "X!"=> C.side N p
lemma how_many {w:Cover}(S: Finset (Site (C.side N p)))(hf: ∀ x∈S, dist (C.S.place x) (C.S.gridPoint j w)≤ α! j/16): S.card≤ (U ht p).count.val^4:=by
   let v:=U ht p; have hh(x)(hx:x∈S): v.parent x=Lattice.wrap _ w:= owner v _ _ (by have he := mesh_fit ht (hf x hx); have hp : 0 < v.count.val:= v.count.property; change 2*separation x _ < v.count.val; change _ ≤ v.count.val/16 at he; have hv:separation x (v.embed (Lattice.wrap _ w))≤ v.count.val/16:= he; omega)
   have he:=card_image_of_injOn (f:=v.residue) (s:=S) (fun x hx y hy h=> (v.unpack_at x).symm.trans ((congr_arg v.assemble (show (v.parent x,v.residue x)=(v.parent y,v.residue y) from Prod.ext ((hh x hx).trans (hh y hy).symm) h)).trans (v.unpack_at y)))
   rw [←he,←site_card v.count]; exact Finset.card_le_univ _
end
namespace Poem
variable (D:Poem C j)
lemma key_one : Injective D.key:=by
   have hv:D.template∈ conf _:=D.fits (fun i=> by rw [show points _=D.template from rfl, dist_self]; exact div_nonneg (C.S.a_pos _).le (by norm_num)); exact fun i k hx=> hv (congr_arg (C.S.gridPoint j) hx)
lemma placed : ∀ᶠ p:ℕ in atTop, Injective (κ (C.side j p) ∘ D.key):=by
   filter_upwards [eventually_all.mpr (fun i=> C.S.radius_diverges.eventually_gt_atTop ‖D.template i‖)] with p hp i k hh; exact D.key_one ((reads_grid (p:=p) rfl (hp i)).symm.trans ((congr_arg _ hh).trans (reads_grid (p:=p) rfl (hp k))))
local notation "I"=> Fin D.n
local notation "X"=> C.side N p
-- cost for post canvas
abbrev annulus (D:Poem C j)(N p:ℕ)(k: Fin D.n): Finset (Site (C.side N p)):= Finset.univ.filter fun i=> C.S.place i ∈ tsupport (D.post k).val
lemma annulus_count (hn:j ≤ N) (k:I): (annulus D N p k).card ≤ (U hn p).count.val^4 := how_many hn _ (fun _ hi=> (D.tucked k (Finset.mem_filter.mp hi).2))
lemma annulus_fits (hn:j ≤ N) (k:I){x:Site (C.side N p)}(hx:x∈annulus D N p k) : x∈((T C.S p hn 0).margin (Lattice.wrap (C.side j p) (D.key k.succ)) ((U hn p).count.val/8)):=margin_fit hn (u:=D.key k.succ) (D.tucked k ((Finset.mem_filter.mp hx).2))
-- limit geometries are fixed here still; period does not grow Asp j.N. combined estimates pay WM ν.
end Poem
end YM.RG05Readout.Bay
