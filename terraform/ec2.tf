# upload the public half of the ssh key deploy.sh uses
resource "aws_key_pair" "main" {
  key_name = "proofbase"
  public_key = file(pathexpand(var.public_key_path))
}

# find the newest amazon linux 2023 image
data "aws_ami" "al2023" {
  most_recent = true
  owners = ["amazon"]
  filter {
    name = "name"
    values = ["al2023-ami-2023.*-x86_64"]
  }
}

# the ec2 instance that runs the app
resource "aws_instance" "app" {
  ami = data.aws_ami.al2023.id
  # 4 vCPU, 16GB ram
  instance_type = "t3.xlarge"
  key_name = aws_key_pair.main.key_name
  vpc_security_group_ids = [aws_security_group.app.id]
  associate_public_ip_address = true

  root_block_device {
    volume_size = 100
    volume_type = "gp3"
  }

  # runs once on first boot: install docker so deploy.sh can build and run the image
  user_data = <<-EOF
    #!/bin/bash
    dnf install -y docker
    systemctl enable --now docker
  EOF
}
