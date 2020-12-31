#![allow(clippy::many_single_char_names)]

use std::mem::MaybeUninit;

use coca::storage::Capacity;
use coca::{Arena, ArenaDeque, ArenaVec};

coca::index_type! { VertexID: u32 }

type Vertex = (f32, f32, f32);
type Face = (VertexID, VertexID, VertexID);
const fn face(a: u32, b: u32, c: u32) -> Face {
    (VertexID(a), VertexID(b), VertexID(c))
}

struct Mesh<'a> {
    vertices: ArenaVec<'a, Vertex, VertexID>,
    faces: ArenaVec<'a, Face, u32>,
}

fn generate_icosphere<'a>(arena: &mut Arena<'a>, subdivision_frequency: u32) -> Mesh<'a> {
    assert!(subdivision_frequency.is_power_of_two());

    let triangulation_number = subdivision_frequency.pow(2);
    let n_vertices = 10 * triangulation_number + 2;
    let mut vertices: ArenaVec<'_, Vertex, VertexID> = arena.vec(VertexID(n_vertices));

    let n_faces = 20 * triangulation_number;
    let mut faces: ArenaDeque<'_, Face, u32> = arena.deque(n_faces);

    // each edge's midpoint is calculated twice, once for each adjacent face
    // so we can cache the calculated midpoint the first time,
    // and remove it from the cache when it is retrieved
    //
    // this way, the maximum number of midpoints stored at any point is
    // the number of edges of the icosphere with half the final subdivision
    // frequency:

    let mut tmp = arena.make_sub_arena();
    let mut edge_subdivision_cache: ArenaVec<(VertexID, VertexID, VertexID), u32> =
        tmp.vec(30 * (subdivision_frequency / 2).pow(2));

    fn subdivide_edge(
        a: VertexID,
        b: VertexID,
        vertices: &mut ArenaVec<'_, Vertex, VertexID>,
        cache: &mut ArenaVec<'_, (VertexID, VertexID, VertexID), u32>,
    ) -> VertexID {
        let (idx_a, idx_b) = if a.as_usize() < b.as_usize() {
            (a, b)
        } else {
            (b, a)
        };

        if let Some(idx) = cache
            .iter()
            .position(|&(fst, snd, _)| fst == idx_a && snd == idx_b)
        {
            cache.remove(idx as u32).2
        } else {
            let a = vertices[idx_a];
            let b = vertices[idx_b];

            let x = (a.0 + b.0) / 2.0;
            let y = (a.1 + b.1) / 2.0;
            let z = (a.2 + b.2) / 2.0;

            let len = (x.powi(2) + y.powi(2) + z.powi(2)).sqrt();
            let x = x / len;
            let y = y / len;
            let z = z / len;

            let idx_mid = VertexID::from_usize(vertices.len());
            vertices.push((x, y, z));

            cache.push((idx_a, idx_b, idx_mid));
            idx_mid
        }
    }

    {
        // Initialization: start with a regular icosahedron
        // From Wikipedia: "The vertices of an icosahedron centered at the
        // origin with an edge-length of 2 and a circumradius of `(phi + 2).sqrt()`
        // are the circular permutations of `(0, +/- 1, +/- phi)`"
        // https://en.wikipedia.org/wiki/Regular_icosahedron#Cartesian_coordinates

        // we start with the normalized coordinates, so that the distance from
        // each vertex to the origin equals one
        let phi = (1.0 + 5.0f32.sqrt()) / 2.0;
        let len = (1.0 + phi.powi(2)).sqrt();

        let one = 1.0 / len;
        let phi = phi / len;

        vertices.push((-one, phi, 0.0));
        vertices.push((one, phi, 0.0));
        vertices.push((-one, -phi, 0.0));
        vertices.push((one, -phi, 0.0));

        vertices.push((0.0, -one, phi));
        vertices.push((0.0, one, phi));
        vertices.push((0.0, -one, -phi));
        vertices.push((0.0, one, -phi));

        vertices.push((phi, 0.0, -one));
        vertices.push((phi, 0.0, one));
        vertices.push((-phi, 0.0, -one));
        vertices.push((-phi, 0.0, one));

        faces.push_back(face(0, 11, 5));
        faces.push_back(face(0, 5, 1));
        faces.push_back(face(0, 1, 7));
        faces.push_back(face(0, 7, 10));
        faces.push_back(face(0, 10, 11));

        faces.push_back(face(1, 5, 9));
        faces.push_back(face(5, 11, 4));
        faces.push_back(face(11, 10, 2));
        faces.push_back(face(10, 7, 6));
        faces.push_back(face(7, 1, 8));

        faces.push_back(face(3, 9, 4));
        faces.push_back(face(3, 4, 2));
        faces.push_back(face(3, 2, 6));
        faces.push_back(face(3, 6, 8));
        faces.push_back(face(3, 8, 9));

        faces.push_back(face(4, 9, 5));
        faces.push_back(face(2, 4, 11));
        faces.push_back(face(6, 2, 10));
        faces.push_back(face(8, 6, 7));
        faces.push_back(face(9, 8, 1));
    }

    let mut threshold = 10000;
    while !faces.is_full() {
        let tri = faces.pop_front().unwrap();
        let a = subdivide_edge(tri.0, tri.1, &mut vertices, &mut edge_subdivision_cache);
        let b = subdivide_edge(tri.1, tri.2, &mut vertices, &mut edge_subdivision_cache);
        let c = subdivide_edge(tri.2, tri.0, &mut vertices, &mut edge_subdivision_cache);

        faces.push_back((tri.0, a, c));
        faces.push_back((tri.1, b, a));
        faces.push_back((tri.2, c, b));
        faces.push_back((a, b, c));

        if vertices.len() > threshold {
            println!(
                "generated {} / {} vertices",
                vertices.len(),
                vertices.capacity()
            );
            threshold += 10000;
        }
    }

    assert!(edge_subdivision_cache.is_empty());
    assert!(vertices.is_full());

    let faces = unsafe {
        let (storage, _, len) = faces.into_raw_parts();
        ArenaVec::from_raw_parts(storage, len)
    };

    Mesh { vertices, faces }
}

fn main() {
    let mut backing = vec![MaybeUninit::<u8>::uninit(); 8 * 1024 * 1024];
    let mut arena = Arena::from(&mut backing[..]);
    let icosphere = generate_icosphere(&mut arena, 128);

    // Verify the generated mesh is indeed an icosphere:

    // 1. count the number of neighbours for each vertex
    //    this is equivalent to counting the faces each vertex is a part of:
    //    two other vertices from the same face are neighbours (i.e. connected
    //    by an edge), but each edge also connects two faces;
    //    these factors cancel out

    let mut neighbour_counts = arena.array(0u32, icosphere.vertices.len());
    for tri in icosphere.faces {
        neighbour_counts[tri.0.as_usize()] += 1;
        neighbour_counts[tri.1.as_usize()] += 1;
        neighbour_counts[tri.2.as_usize()] += 1;
    }

    // 2. check the distribution of numbers-of-neighbours
    //    each vertex added during the subdivision phase should have six
    //    neighbours; the 12 vertices of an icosahedron have five neighbors
    //    each, and the subdivision process does not change this property

    let mut num_five_neighbours = 0u32;
    let mut num_six_neighbours = 0u32;
    for (vertex_id, &count) in neighbour_counts.iter().enumerate() {
        if count == 5 {
            assert!(vertex_id < 12);
            num_five_neighbours += 1;
        } else if count == 6 {
            num_six_neighbours += 1;
        } else {
            panic!("vertex {} has {} neighbours", vertex_id, count);
        }
    }

    assert_eq!(num_five_neighbours, 12);
    assert_eq!(num_six_neighbours, icosphere.vertices.len() as u32 - 12);

    println!("OK.");
}
