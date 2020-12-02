use coca::Arena;

use std::mem::{size_of, MaybeUninit};

fn calc_huff_encoded_size(input: &[u8]) -> usize {
    const MEM_FOR_FREQS_AND_CODELEN: usize = (1 + 256 + 256) * size_of::<usize>(); // + 1 usize for alignment
    const MEM_FOR_TREES: usize = 512 * size_of::<CodeTree>();
    const ARENA_SIZE: usize = MEM_FOR_FREQS_AND_CODELEN + MEM_FOR_TREES;
    
    let mut backing = Box::new([MaybeUninit::<u8>::uninit(); ARENA_SIZE]);
    let mut arena = Arena::from(&mut backing[..]);

    let mut freqs = arena.array(0isize, 256);
    for &b in input {
        freqs[b as usize] += 1;
    }

    #[derive(Debug)]
    enum CodeTree<'a> {
        Symbol{sym: u8},
        Composite{left: coca::Box<'a, CodeTree<'a>>, right: coca::Box<'a, CodeTree<'a>>},
    }

    let mut queue = arena.vec(256usize);
    for (idx, freq) in freqs.iter().enumerate() {
        if *freq == 0 { continue; }
        let leaf_node = arena.alloc(CodeTree::Symbol{sym: idx as u8});
        queue.push((leaf_node, *freq));
    }

    queue.sort_by_key(|&(_, freq)| -freq);

    while queue.len() > 1 {
        let (left, freq_l) = queue.pop().unwrap();
        let (right, freq_r) = queue.pop().unwrap();

        let parent_node = arena.alloc(CodeTree::Composite{left, right});
        let combined_freq = freq_l + freq_r;

        let search_result = queue.binary_search_by_key(&-combined_freq, |(_, f)| -f);
        let insertion_index = match search_result {
            Ok(i) => i,
            Err(i) => i,
        };

        queue.insert(insertion_index, (parent_node, combined_freq));
    }

    fn find_code_lens(node: &CodeTree, recursion_level: usize, code_len_table: &mut [usize; 256]) {
        match &*node {
            CodeTree::Symbol { sym } => code_len_table[*sym as usize] = recursion_level,
            CodeTree::Composite { left, right } => {
                find_code_lens(left.as_ref(), recursion_level + 1, code_len_table);
                find_code_lens(right.as_ref(), recursion_level + 1, code_len_table);
            }
        }
    }

    let mut code_lens = arena.alloc([usize::MAX; 256]);
    find_code_lens(queue.pop().unwrap().0.as_ref(), 0, code_lens.as_mut());
    let bits_needed: usize = (0..256).map(|i| code_lens[i] * freqs[i] as usize).sum();

    (bits_needed + 7) / 8
}

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("Usage: huffman <InputFile>");
        std::process::exit(1);
    }

    let input_file_path = &args[1];
    let input_file_content = match std::fs::read(input_file_path) {
        Ok(content) => content,
        Err(e) => {
            println!("Failed to read file: {}", e);
            std::process::exit(1);
        }
    };

    println!("Uncompressed: {} bytes", input_file_content.len());
    println!("Huffman compressed: {} bytes", calc_huff_encoded_size(&input_file_content));
}
