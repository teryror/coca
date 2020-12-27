use coca::Arena;

use std::mem::{size_of, MaybeUninit};

const SOURCE: &str = include_str!("huffman.rs");

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
        Symbol {
            sym: u8,
        },
        Composite {
            left: coca::Box<'a, CodeTree<'a>>,
            right: coca::Box<'a, CodeTree<'a>>,
        },
    }

    struct Item<'a>(isize, coca::Box<'a, CodeTree<'a>>);
    impl<'a> std::cmp::PartialEq for Item<'a> {
        fn eq(&self, rhs: &Self) -> bool {
            self.0.eq(&rhs.0)
        }
    }
    impl<'a> std::cmp::PartialOrd for Item<'a> {
        fn partial_cmp(&self, rhs: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(rhs))
        }
    }
    impl<'a> std::cmp::Eq for Item<'a> {}
    impl<'a> std::cmp::Ord for Item<'a> {
        fn cmp(&self, rhs: &Self) -> std::cmp::Ordering {
            self.0.cmp(&rhs.0).reverse()
        }
    }

    let mut items = arena.vec(256usize);
    for (idx, freq) in freqs.iter().enumerate() {
        if *freq == 0 {
            continue;
        }
        let leaf_node = arena.alloc(CodeTree::Symbol { sym: idx as u8 });
        items.push(Item(*freq, leaf_node));
    }

    let mut queue = coca::ArenaHeap::<Item<'_>, _>::from(items);
    while queue.len() > 1 {
        let Item(freq_l, left) = queue.pop().unwrap();
        let Item(freq_r, right) = queue.pop().unwrap();

        let parent_node = arena.alloc(CodeTree::Composite { left, right });
        let combined_freq = freq_l + freq_r;

        queue.push(Item(combined_freq, parent_node));
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
    find_code_lens(queue.pop().unwrap().1.as_ref(), 0, code_lens.as_mut());
    let bits_needed: usize = (0..256).map(|i| code_lens[i] * freqs[i] as usize).sum();

    (bits_needed + 7) / 8
}

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let input_file_content = match args.len() {
        1 => std::vec::Vec::from(SOURCE.as_bytes()),
        2 => {
            let input_file_path = &args[1];
            match std::fs::read(input_file_path) {
                Ok(content) => content,
                Err(e) => {
                    println!("Failed to read file: {}", e);
                    std::process::exit(1);
                }
            }
        }
        _ => {
            println!("Usage: huffman <InputFile>");
            std::process::exit(1);
        }
    };

    println!("Uncompressed: {} bytes", input_file_content.len());
    println!(
        "Huffman compressed: {} bytes",
        calc_huff_encoded_size(&input_file_content)
    );
}
